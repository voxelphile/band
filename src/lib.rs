//Hello, band!
#![allow(dead_code)]
#![feature(return_position_impl_trait_in_trait, fn_traits, test)]

pub use band_proc_macro::*;
use core::slice;
use crossbeam::channel::*;
use derive_more::*;
use itertools::*;
use std::{
    any::{type_name, TypeId},
    arch,
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    convert::identity,
    error::Error,
    hint::black_box,
    iter,
    marker::PhantomData,
    mem,
    process::Termination,
    ptr,
    thread::{self, JoinHandle},
    time::{Duration, Instant}, sync::{atomic::AtomicUsize, Arc},
};

pub type Identifier = usize;
pub type Generation = usize;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Debug)]
pub struct Entity(Identifier, Generation);

pub struct Entities {
    cursor: Box<dyn Iterator<Item = Identifier> + 'static + Send + Sync>,
    free: HashSet<Entity>,
    dead: HashSet<Entity>,
}

impl Default for Entities {
    fn default() -> Self {
        Self {
            cursor: Box::new(0..),
            free: HashSet::new(),
            dead: HashSet::new(),
        }
    }
}

impl Entities {
    pub fn spawn(&mut self) -> Entity {
        if let Some(entity) = self.free.iter().next().cloned() {
            self.free.remove(&entity);
            entity
        } else {
            Entity(self.cursor.next().unwrap(), 0)
        }
    }

    pub fn despawn(&mut self, entity: Entity) -> bool {
        if self.dead.contains(&entity) {
            return false;
        }
        self.dead.insert(entity);
        let Entity(identifier, generation) = entity;
        let entity = Entity(identifier, generation + 1);
        if self.free.contains(&entity) {
            false
        } else {
            self.free.insert(entity);
            true
        }
    }
}

pub type DataId = TypeId;
pub type DataName = &'static str;

pub trait DataInternal {
    unsafe fn as_raw(&self) -> &[u8] {
        slice::from_raw_parts(self as *const _ as *const u8, mem::size_of_val(self))
    }
    unsafe fn as_raw_mut(&mut self) -> &mut [u8] {
        slice::from_raw_parts_mut(self as *mut _ as *mut u8, mem::size_of_val(self))
    }
    unsafe fn as_ref(ptr: *const u8) -> &'static Self
    where
        Self: Sized,
    {
        ptr.cast::<Self>().as_ref().unwrap()
    }
    unsafe fn as_mut(ptr: *mut u8) -> &'static mut Self
    where
        Self: Sized,
    {
        ptr.cast::<Self>().as_mut().unwrap()
    }
}

pub trait Data: DataInternal + 'static + Send + Sync {}

pub trait Component: Data {}

pub trait DataExt: Data {
    fn id() -> DataId {
        DataId::of::<Self>()
    }
    fn size() -> usize
    where
        Self: Sized,
    {
        mem::size_of::<Self>()
    }
    fn name() -> DataName {
        type_name::<Self>()
    }
    fn info() -> DataInfo
    where
        Self: Sized,
    {
        DataInfo {
            id: Self::id(),
            name: Self::name(),
            size: Self::size(),
        }
    }
}

impl<T: Data> DataInternal for T {}
impl<T: Data> DataExt for T {}
impl<T: Data> Data for &'static T {}
impl<T: Data> Data for &'static mut T {}

pub type BoxedComponent = Box<dyn Component>;

pub struct ComponentPack(DataInfo, BoxedComponent);
#[derive(Clone, Copy)]
pub struct DataInfo {
    id: DataId,
    name: DataName,
    size: usize,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deref, DerefMut, Default)]
pub struct Archetype(Vec<DataId>);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Access {
    Ref(DataId),
    Mut(DataId),
}

impl Access {
    fn overlaps(&self, other: &Self) -> bool {
        use Access::*;
        match (self, other) {
            (Ref(_), Ref(_)) => false,
            (Ref(x), Mut(y)) | (Mut(x), Ref(y)) | (Mut(x), Mut(y)) => x == y,
        }
    }
}

impl Archetype {
    fn size(&self, data_info: &HashMap<DataId, DataInfo>) -> usize {
        self.iter().map(|id| data_info[id].size).sum()
    }
    fn translations(&self, data_info: &HashMap<DataId, DataInfo>) -> Vec<usize> {
        (0..=self.len())
            .map(|n| self.iter().take(n).map(|id| data_info[id].size).sum())
            .collect()
    }
    fn ordered_position(&self, id: &DataId) -> usize {
        match self.binary_search_by(|probe| probe.cmp(&id)) {
            Ok(i) => i,
            Err(i) => i,
        }
    }
    fn is_superset(&self, other: &Archetype) -> bool {
        other.iter().all(|probe| self.contains(&probe))
    }
}

pub struct Storage {
    pub(crate) archetype: Archetype,
    pub(crate) entries: usize,
    pub(crate) individual_size: usize,
    pub(crate) total_size: usize,
    pub(crate) pad_size: usize,
    pub(crate) translations: Vec<usize>,
    pub(crate) data: Vec<u8>,
    pub(crate) mapping: Vec<Entity>,
    pub(crate) secondary_mapping: HashMap<Entity, usize>,
    pub(crate) table: Vec<Vec<BoxedComponent>>,
}

pub const CACHE_LINE: usize = 64;

impl Storage {
    pub fn new(archetype: Archetype, data_info: &HashMap<DataId, DataInfo>) -> Self {
        let individual_size = archetype.size(data_info);
        let total_size =
            ((individual_size as f64 / CACHE_LINE as f64).ceil() * CACHE_LINE as f64) as usize;
        let pad_size = total_size - individual_size;
        let translations = archetype.translations(data_info);
        Self {
            archetype,
            entries: 0,
            translations,
            individual_size,
            total_size,
            pad_size,
            data: vec![],
            mapping: vec![],
            secondary_mapping: HashMap::new(),
            table: vec![],
        }
    }
    pub fn push(&mut self, entity: Entity, mut data: Vec<u8>, repr: Vec<BoxedComponent>) {
        if self.total_size == 0 {
            return;
        }

        assert_eq!(data.len(), self.individual_size);

        data.extend(iter::repeat(0u8).take(self.pad_size));

        let idx = self.data.len() / self.total_size;
        self.data.extend(data);
        self.mapping.push(entity);
        self.secondary_mapping.insert(entity, idx);
        self.table.push(repr);

        self.entries += 1;
    }

    pub fn remove(&mut self, entity: Entity) -> (Vec<u8>, Vec<BoxedComponent>) {
        if self.total_size == 0 {
            return (vec![], vec![]);
        }
        let original_len = self.data.len() / self.total_size;
        //TODO this operation can maybe be optimized
        let idx = self.secondary_mapping.remove(&entity).unwrap();
        self.mapping.swap_remove(idx);
        let mut table = self.table.swap_remove(idx);
        if idx != original_len - 1 {
            self.secondary_mapping.insert(self.mapping[idx], idx);
        }

        let mut removed_data = self
            .data
            .drain(idx * self.total_size..(idx + 1) * self.total_size)
            .collect::<Vec<_>>();

        if idx != original_len - 1 {
            let from = original_len - 1;

            let end = self.data[(from - 1) * self.total_size..].to_vec();

            self.data
                .splice(idx * self.total_size..idx * self.total_size, end);
            self.data.resize(self.data.len() - self.total_size, 0);
        }

        removed_data.resize(self.individual_size, 0u8);

        for (i, boxed_data) in table.iter_mut().enumerate() {
            let start = self.translations[i];
            let end = self.translations[i + 1];
            unsafe { boxed_data.as_raw_mut() }.copy_from_slice(&removed_data[start..end]);
        }

        self.entries -= 1;

        (removed_data, table)
    }
}

pub trait Bundle {
    fn into_component_packs(self) -> Vec<ComponentPack>;
}

macro_rules! impl_bundle {
    ($($items:ident),*) => {
        #[allow(non_snake_case)]
        impl<$($items: Component),*> Bundle for ($($items),*,)
        {
            fn into_component_packs(self) -> Vec<ComponentPack> {
                let infos =
                vec![
                    $($items::info()),*
                ];
                let ($($items),*,) = self;
                let data = vec![
                    $(Box::new($items) as Box<dyn Component>),*
                ];
                infos.into_iter().zip(data.into_iter()).map(|(info, data)| ComponentPack(info, data)).collect()
            }
        }

        impl_bundle!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_bundle!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_bundle!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub enum Command {
    Spawn(Vec<ComponentPack>),
    Insert(Entity, Vec<ComponentPack>),
}

pub struct Commands {
    tx: Sender<Command>,
}

impl Commands {
    fn spawn(&self, bundle: impl Bundle) {
        self.tx.send(Command::Spawn(bundle.into_component_packs()));
    }
    fn insert(&self, entity: Entity, bundle: impl Bundle) {
        self.tx
            .send(Command::Insert(entity, bundle.into_component_packs()));
    }
}

type ReturnStorage = (Sender<(Archetype, Storage)>, Receiver<(Archetype, Storage)>);

pub struct Registry {
    entities: Entities,
    data_info: HashMap<DataId, DataInfo>,
    storage: HashMap<Archetype, Storage>,
    mapping: HashMap<Entity, Archetype>,
    cmds: (Sender<Command>, Receiver<Command>),
    return_storage: ReturnStorage,
}

impl Registry {
    fn commands(&self) -> Commands {
        let (tx, _) = &self.cmds;
        let tx = tx.clone();
        Commands { tx }
    }
    fn return_storage(&mut self) {
        while let Ok(pair) = self.return_storage.1.try_recv() {
            self.storage.extend(iter::once(pair));
        }
    }
    fn flush_commands(&mut self) {
        while let Ok(command) = self.cmds.1.try_recv() {
            match command {
                Command::Spawn(bundle) => {
                    let entity = self.spawn();
                    self.insert(entity, bundle);
                }
                Command::Insert(entity, bundle) => {
                    self.insert(entity, bundle);
                }
            }
        }
    }
    fn spawn(&mut self) -> Entity {
        let entity = self.entities.spawn();
        self.mapping.insert(entity, Archetype::default());
        entity
    }
    fn insert(&mut self, entity: Entity, mut bundle: Vec<ComponentPack>) {
        self.return_storage();

        let Some(mut archetype) = self.mapping.remove(&entity) else {
            return;
        };

        let (mut data, mut table) = if archetype.len() != 0 {
            self.storage.get_mut(&archetype).unwrap().remove(entity)
        } else {
            (vec![], vec![])
        };

        for ComponentPack(info, _) in &bundle {
            let DataInfo { id, .. } = info;

            let position = archetype.ordered_position(id);
            archetype.insert(position, *id);

            self.data_info.insert(*id, *info);
        }

        let translations = archetype.translations(&self.data_info);

        bundle.sort_by(|a, b| {
            translations[archetype.iter().position(|p| p == &a.0.id).unwrap()]
                .cmp(&translations[archetype.iter().position(|p| p == &b.0.id).unwrap()])
        });

        for ComponentPack(_, boxed_component) in bundle {
            data.extend(unsafe { boxed_component.as_raw() });
            table.push(boxed_component);
        }

        self.storage
            .entry(archetype.clone())
            .or_insert_with(|| Storage::new(archetype.clone(), &self.data_info))
            .push(entity, data, table);
        self.mapping.insert(entity, archetype);
    }
}

impl Default for Registry {
    fn default() -> Self {
        Self {
            entities: Default::default(),
            data_info: Default::default(),
            storage: Default::default(),
            mapping: Default::default(),
            return_storage: unbounded(),
            cmds: unbounded(),
        }
    }
}

pub type Precedence = isize;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Filtered {
    Include,
    Exclude,
}

impl From<Filtered> for bool {
    fn from(value: Filtered) -> Self {
        matches!(value, Filtered::Include)
    }
}

pub trait Filter: 'static + Send + Sized {
    fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered;
}

impl Filter for () {
    fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered {
        Filtered::Include
    }
}

pub struct Superset;

impl Filter for Superset {
    fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered {
        query_archetype.is_superset(storage_archetype).then_some(Filtered::Include).unwrap_or(Filtered::Exclude)
    }
}

pub struct With<C: Component> {
    marker: PhantomData<C>
}

impl<C: Component> Filter for With<C> {
    fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered {
        let mut extra_archetype = query_archetype.clone();
        extra_archetype.push(C::id());
        Superset::validity(&extra_archetype, storage_archetype)
    }
}

pub struct Without<C: Component> {
    marker: PhantomData<C>
}

impl<C: Component> Filter for Without<C> {
    fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered {
        storage_archetype.contains(&C::id()).then_some(Filtered::Exclude).unwrap_or(Filtered::Include)
    }
}


macro_rules! impl_filter {
    ($($items:ident),*) => {
        #[allow(non_snake_case)]
        impl<$($items: Filter),*> Filter for ($($items,)*) {
            fn validity(query_archetype: &Archetype, storage_archetype: &Archetype) -> Filtered {
                ($(matches!($items::validity(query_archetype, storage_archetype), Filtered::Exclude)) && *).then_some(Filtered::Exclude).unwrap_or(Filtered::Include)
            }
        }

        impl_filter!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_filter!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_filter!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub struct Query<Q: Queryable, F: Filter = ((), Superset)>
where
    Self: 'static,
{
    storage: Vec<(Archetype, Storage, Vec<usize>)>,
    tx: Sender<(Archetype, Storage)>,
    marker: PhantomData<(Q, F)>,
}

impl<Q: Queryable, F: Filter> Drop for Query<Q, F> {
    fn drop(&mut self) {
        for pair in self.storage.drain(..).map(|(x, y, _)| (x, y)) {
            self.tx.send(pair).expect("failed to return storage");
        }
    }
}

impl<Q: Queryable, F: Filter> IntoIterator for Query<Q, F> {
    type Item = Q;
    type IntoIter = QueryIter<Q, F>;
    fn into_iter(self) -> Self::IntoIter {
        QueryIter {
            query: self,
            inner: 0,
            outer: 0,
        }
    }
}

pub struct QueryIter<Q: Queryable, F: Filter> {
    query: Query<Q, F>,
    inner: usize,
    outer: usize,
}

pub trait Queryable: DataExt + Send + Sync + 'static + Sized {
    type Target: DataExt;
    fn access(access: &mut Vec<Access>);
    fn archetype(archetype: &mut Archetype) {
        let position = archetype.ordered_position(&Self::Target::id());
        archetype.insert(position, Self::Target::id());
    }
    fn order(archetype: &Archetype, order: &mut Vec<usize>) {
        dbg!("---");
        order.push(
            archetype
                .iter()
                .position(|probe| dbg!(probe) == dbg!(&Self::Target::id()))
                .unwrap(),
        )
    }
    fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
    where
        Self: Sized;
}

pub trait QueryableExt: Queryable {
    fn query_filter<F: Filter>(registry: &mut Registry) -> Query<Self, (F, Superset)>
    where
        Self: Sized,
    {
        registry.return_storage();

        let mut query_archetype = Default::default();
        Self::archetype(&mut query_archetype);

        let mut storage_archetypes = vec![];
        for storage_archetype in registry.storage.keys() {
            if matches!(F::validity(&query_archetype, storage_archetype), Filtered::Include)  {
                storage_archetypes.push(storage_archetype.clone());
            }
        }

        let storage = storage_archetypes
            .into_iter()
            .map(|archetype| {
                let mut order = vec![];
                Self::order(&archetype, &mut order);

                let storage = registry.storage.remove(&archetype).unwrap();
                let mut translations = vec![];

                for order in order {
                    translations.push(storage.translations[order]);
                }

                (archetype.clone(), storage, translations)
            })
            .collect();

        let (tx, _) = &registry.return_storage;
        let tx = tx.clone();
        Query {
            storage,
            tx,
            marker: PhantomData,
        }
    }
    fn query(registry: &mut Registry) -> Query<Self, ((), Superset)> {
        Self::query_filter::<()>(registry)
    }
}

impl<Q: Queryable> QueryableExt for Q {}

impl<Q: Queryable, F: Filter> Iterator for QueryIter<Q, F> {
    type Item = Q;

    fn next(&mut self) -> Option<Self::Item> {
        if self.query.storage.is_empty() {
            None?
        }

        if self.outer >= self.query.storage.len() {
            None?
        }

        let (_, storage, _) = &self.query.storage[self.outer];

        if self.inner >= storage.entries {
            self.outer += 1;
            self.inner = 0;
        }

        if self.outer >= self.query.storage.len() {
            None?
        }

        self.inner += 1;

        let (_, storage, translations) = &mut self.query.storage[self.outer];

        let ptr = storage.data.as_mut_ptr();

        unsafe {
            Some(<Q as Queryable>::get(
                ptr.add(self.inner * storage.total_size),
                translations,
                &mut 0,
            ))
        }
    }
}

impl<T: Component> Queryable for &'static T {
    type Target = T;
    fn access(access: &mut Vec<Access>) {
        access.push(Access::Ref(Self::Target::id()))
    }
    fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
    where
        Self: Sized,
    {
        let component = unsafe { Self::Target::as_ref(ptr.add(translations[*idx])) };
        *idx += 1;
        component
    }
}
impl<T: Component> Queryable for &'static mut T {
    type Target = T;
    fn access(access: &mut Vec<Access>) {
        access.push(Access::Mut(Self::Target::id()))
    }
    fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
    where
        Self: Sized,
    {
        let component = unsafe { Self::Target::as_mut(ptr.add(translations[*idx])) };
        *idx += 1;
        component
    }
}

macro_rules! impl_queryable {
    ($($items:ident),*) => {
    #[allow(non_snake_case)]
    impl<$($items: Data),*> Data for ($($items),*,) {}
    impl<$($items: Queryable),*> Queryable for ($($items),*,)
        {
            type Target = Self;
            fn access(access: &mut Vec<Access>) {
                $($items::access(access);)*
            }
            fn archetype(archetype: &mut Archetype) {
                $($items::archetype(archetype);)*
            }
            fn order(archetype: &Archetype, order: &mut Vec<usize>) {
                $($items::order(archetype, order);)*
            }
            fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
            where
                Self: Sized,
            {
                (
                    $($items::get(ptr, translations, idx),)*
                )
            }
        }

        impl_queryable!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_queryable!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_queryable!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub struct SystemQuery<Q: Queryable, F: Filter> {
    marker: PhantomData<(Q, F)>,
}

pub trait SystemIn: 'static
where
    Self: Send,
{
    fn prepare_execution(registry: &mut Registry) -> Self;
    fn access(access: &mut Vec<Access>);
}

impl SystemIn for () {
    fn prepare_execution(registry: &mut Registry) -> Self {}
    fn access(access: &mut Vec<Access>) {}
}

macro_rules! impl_system_in {
    ($($items:ident),*) => {
    #[allow(unused_parens)] // This is added because the nightly compiler complains
    #[allow(non_snake_case)] // This is added because the nightly compiler complains
        impl<$($items: SystemIn),*> SystemIn for ($($items),*,)
        {
            fn prepare_execution(registry: &mut Registry) -> Self {
                $(let $items = $items::prepare_execution(registry);)*
                ($($items),*,)
            }
            fn access(access: &mut Vec<Access>) {
                $($items::access(access);)*
            }
        }

        impl_system_in!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_system_in!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_system_in!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub trait SystemOut: 'static
where
    Self: Send,
{
    fn handle(self, name: &str);
}

impl SystemOut for () {
    fn handle(self, _: &str) {}
}

impl<E: Error + Send + 'static> SystemOut for Result<(), E> {
    fn handle(self, name: &str) {
        self.expect(&format!("System `{name}` failed to execute"))
    }
}

pub trait System<In: SystemIn, Out: SystemOut>: Send {
    fn prepare_execution(&self, registry: &mut Registry) -> In;
    fn execute(&self, input: In) -> Out;
}

macro_rules! impl_system {
    ($($items:ident),*) => {
        impl_fn_system!([$($items),*]);
        impl_system!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_system!($($tail),*);
    };
    (@ $head:ident) => {};
}

macro_rules! impl_fn_system {
    ([$($x:ident),* $(,)?]; [] reversed: [$($y:ident,)*]) => {
        #[allow(non_snake_case)]
        impl<$($x: SystemIn,)* Return: SystemOut, Function: ::std::ops::Fn($($y,)*) -> Return + Send> System<($($x,)*), Return> for Function {
            fn prepare_execution(&self, registry: &mut Registry) -> ($($x),*,) {
                <($($x),*,)>::prepare_execution(registry)
            }
            fn execute(&self, input: ($($x),*,)) -> Return {
                let ($($x),*,) = input;
                self.call(($($y,)*))
            }
        }
    };
    ([$($x:ident),* $(,)?]) => {
        impl_fn_system!([$($x),*]; [$($x),*] reversed: []);
    };
    ([$($x:ident),* $(,)?]; [$head:ident $(, $tail:ident)*] reversed: [$($reversed:ident,)*]) => {
        impl_fn_system!([$($x),*]; [$($tail),*] reversed: [$head, $($reversed,)*]);
    };
}

impl_system!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub trait Flatten {
    type Output;
    fn flatten(self) -> Self::Output;
}

impl Flatten for () {
    type Output = ();
    fn flatten(self) -> Self::Output {
        self
    }
}

macro_rules! cons {
    () => (
        ()
    );
    ($head:tt) => (
        ($head, ())
    );
    ($head:tt, $($tail:tt,)*) => (
        ($head, cons!($($tail,)*))
    );
}

macro_rules! impl_flatten {
    ($($items:ident),*) => {
    #[allow(unused_parens)] // This is added because the nightly compiler complains
        impl<$($items),*> Flatten for cons!($($items,)*)
        {
            type Output = ($($items,)*);
            fn flatten(self) -> Self::Output {
                #[allow(non_snake_case)]
                let cons!($($items,)*) = self;
                ($($items,)*)
            }
        }

        impl_flatten!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_flatten!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_flatten!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

pub trait SystemParam {
    type In;
}

impl SystemParam for () {
    type In = ();
}

macro_rules! impl_system_param {
    ($($items:ident),*) => {
        #[allow(non_snake_case)]
        impl<$($items: SystemParam),*> SystemParam for ($($items),*,)
        {
            type In = ($($items::In),*,);

        }

        impl_system_param!(@ $($items),*);
    };
    (@ $head:ident, $($tail:ident),*) => {
        impl_system_param!($($tail),*);
    };
    (@ $head:ident) => {};
}

impl_system_param!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

impl<Q: Queryable, F: Filter> SystemParam for SystemQuery<Q, F> {
    type In = Query<Q, F>;
}
impl<Q: Queryable, F: Filter> SystemIn for Query<Q, (F, Superset)> {
    fn prepare_execution(registry: &mut Registry) -> Self {
        Q::query_filter::<F>(registry)
    }
    fn access(access: &mut Vec<Access>) {
        Q::access(access)
    }
}

impl SystemParam for Commands {
    type In = Self;
}
impl SystemIn for Commands {
    fn prepare_execution(registry: &mut Registry) -> Self {
        registry.commands()
    }
    fn access(access: &mut Vec<Access>) {}
}

pub struct SystemBuilder<A: Flatten> {
    param: A,
    name: String,
}

pub const UNNAMED: &str = "unnamed";

impl SystemBuilder<()> {
    fn new() -> SystemBuilder<()> {
        Self {
            param: (),
            name: UNNAMED.to_string(),
        }
    }
}

impl<A: Flatten> SystemBuilder<A> {
    fn with_name(self, name: impl ToString) -> Self {
        Self {
            name: name.to_string(),
            ..self
        }
    }

    fn with_query<Q: Queryable>(self) -> SystemBuilder<(SystemQuery<Q, ((), Superset)>, A)>
    where 
    (SystemQuery<Q, ((), Superset)>, A): Flatten,
    {
        Self::with_query_filter(self)
    }

    fn with_query_filter<Q: Queryable, F: Filter>(self) -> SystemBuilder<(SystemQuery<Q, F>, A)>
    where
        (SystemQuery<Q, F>, A): Flatten,
    {
        SystemBuilder::<(SystemQuery<Q, F>, A)> {
            param: (
                SystemQuery {
                    marker: PhantomData,
                },
                self.param,
            ),
            name: self.name,
        }
    }

    fn build<R: SystemOut>(
        self,
        system: impl System<<A::Output as SystemParam>::In, R> + 'static,
    ) -> Box<dyn Schedulable>
    where
        A::Output: SystemParam,
        <A::Output as SystemParam>::In: SystemIn,
    {
        Box::new(SystemSchedulable {
            system: Box::new(system),
            input: None,
            name: self.name,
        })
    }
}

pub struct SystemSchedulable<In: SystemIn, Out: SystemOut> {
    system: Box<dyn System<In, Out>>,
    input: Option<In>,
    name: String,
}

impl<In: SystemIn, Out: SystemOut> Schedulable for SystemSchedulable<In, Out> {
    fn prepare_execution(&mut self, registry: &mut Registry) {
        self.input = Some(self.system.prepare_execution(registry));
    }
    fn execute(&mut self) {
        self.system
            .execute(self.input.take().unwrap())
            .handle(&self.name);
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn access(&self) -> Vec<Access> {
        let mut access = vec![];
        In::access(&mut access);
        access
    }
}

pub trait Schedulable: 'static + Send {
    fn prepare_execution(&mut self, registry: &mut Registry);
    fn execute(&mut self);
    fn name(&self) -> &str;
    fn access(&self) -> Vec<Access>;
}

pub type NodeId = usize;

#[derive(Default)]
pub struct Graph {
    nodes: Vec<Box<dyn Schedulable>>,
    dependencies: Vec<Vec<NodeId>>,
}

impl Graph {
    fn add(&mut self, registry: &Registry, schedulable: Box<dyn Schedulable>) {
        let my_id = self.nodes.len();

        let access = schedulable.access();

        let mut overlaps = HashSet::new();

        for a in &access {
            for b in &access {
                if a != b && a.overlaps(b) && !overlaps.contains(&(*b, *a)) {
                    overlaps.insert((*a, *b));
                }
            }
        }

        if !overlaps.is_empty() {
            let system_name = schedulable.name();
            let mut error = String::new();
            error.push_str(&format!(
                "Overlapping archetypal access was detected in system `{system_name}`. \
                The following overlaps were found:\n"
            ));
            for overlap in &overlaps {
                let first_ref_type = match overlap.0 {
                    Access::Mut(_) => "Mutable reference",
                    Access::Ref(_) => "Reference",
                };
                let first_data_name = registry.data_info[match &overlap.0 {
                    Access::Mut(id) => id,
                    Access::Ref(id) => id,
                }]
                .name;
                let second_ref_type = match overlap.1 {
                    Access::Mut(_) => "mutable reference",
                    Access::Ref(_) => "reference",
                };
                error.push_str(&format!(
                    "\t- {first_ref_type} to `{first_data_name}` overlaps with {second_ref_type} of the same type.\n"
                ))
            }
            panic!("{}", error);
        }

        self.nodes.push(schedulable);

        let mut dependencies = Vec::new();

        'a: for (their_id, them) in self.nodes[..my_id].iter().enumerate().rev() {
            let their_access = them.access();

            for my_access in &access {
                for their_access in &their_access {
                    if my_access.overlaps(their_access) {
                        dependencies.push(their_id);
                        continue 'a;
                    }
                }
            }
        }

        self.dependencies.push(dependencies);
    }
}

pub trait IntoSchedulable<In, Out> {
    fn into_schedulable(self) -> Box<dyn Schedulable>;
}

impl IntoSchedulable<(), ()> for Box<dyn Schedulable> {
    fn into_schedulable(self) -> Box<dyn Schedulable> {
        self
    }
}

impl<In: SystemIn, Out: SystemOut, S: System<In, Out> + 'static> IntoSchedulable<In, Out> for S {
    fn into_schedulable(self) -> Box<dyn Schedulable> {
        Box::new(SystemSchedulable {
            system: Box::new(self),
            input: None,
            name: UNNAMED.to_string(),
        })
    }
}

pub type NodePayload = (NodeId, Box<dyn Schedulable>);

pub struct Schedule<'a> {
    graph: Graph,
    work_tx: Sender<NodePayload>,
    done_rx: Receiver<NodePayload>,
    workers: Vec<JoinHandle<()>>,
    registry: &'a mut Registry,
}
impl<'a> Schedule<'a> {
    fn new(workers: usize, registry: &'a mut Registry) -> Self {
        let (work_tx, work_rx) = unbounded::<NodePayload>();
        let (done_tx, done_rx) = unbounded::<NodePayload>();
        let workers = (0..workers)
            .map(|i| {
                let work_rx = work_rx.clone();
                let done_tx = done_tx.clone();

                thread::Builder::new()
                    .name(format!("Worker {i}"))
                    .spawn(move || loop {
                        let Ok((id, mut node)) = work_rx.try_recv() else {
                            thread::sleep(Duration::from_nanos(1));
                            continue;
                        };

                        node.execute();

                        done_tx
                            .send((id, node))
                            .expect("failed to signal work unit as done");
                    })
                    .expect("failed to start worker")
            })
            .collect::<Vec<_>>();
        Schedule {
            graph: Default::default(),
            work_tx,
            done_rx,
            workers,
            registry,
        }
    }
    fn add<In, Out>(&mut self, schedulable: impl IntoSchedulable<In, Out>) {
        self.graph
            .add(self.registry, schedulable.into_schedulable());
    }
    fn execute(&mut self) {
        let mut executing = Vec::new();

        let not_executed = self.graph.nodes.drain(..).collect::<VecDeque<_>>();
        let mut executed = (0..not_executed.len()).map(|_| None).collect::<Vec<_>>();

        let mut nodes_iter = not_executed.into_iter().enumerate().peekable();

        loop {
            #[allow(clippy::never_loop)]
            'a: loop {
                if let Some((next_id, _)) = nodes_iter.peek() {
                    if executing
                        .iter()
                        .any(|id| self.graph.dependencies[*next_id].contains(id))
                    {
                        self.registry.flush_commands();
                        self.registry.return_storage();
                        break;
                    }
                }

                loop {
                    let id = self.done_rx.try_recv();

                    if id.is_err() && executing.is_empty() {
                        break 'a;
                    }

                    let Ok((id, schedulable)) = id else {
                        continue;
                    };
                    let index = match executing.binary_search(&id) {
                        Err(_) => panic!("not scheduled"),
                        Ok(i) => i,
                    };
                    executing.remove(index);
                    executed[id] = Some(schedulable);
                }
            }

            let Some((id, mut node)) = nodes_iter.next() else {
                break;
            };

            let index = match executing.binary_search(&id) {
                Err(i) => i,
                Ok(_) => panic!("already scheduled"),
            };
            executing.insert(index, id);

            node.prepare_execution(self.registry);

            self.work_tx
                .try_send((id, node))
                .expect("failed to send work unit");
        }
        self.graph.nodes = executed.into_iter().flatten().collect();
        self.registry.flush_commands();
        self.registry.return_storage();
    }
}

#[derive(Component, Debug, PartialEq)]
pub struct TestData1 {
    s: u32,
}
#[derive(Component, Debug, PartialEq)]
pub struct TestData2 {
    s: u32,
}
#[derive(Component, Debug, PartialEq)]
pub struct TestData3 {
    s: u32,
}
#[derive(Component, Debug, PartialEq)]
pub struct TestData4 {
    s: u32,
}   
#[derive(Component, Debug, PartialEq)]
pub struct TestData5 {
    s: u32,
}
#[derive(Component, Debug, PartialEq)]
pub struct DidItSpawn(usize);

extern crate test;
use test::Bencher;
#[bench]
fn benchmark(bencher: &mut Bencher) -> impl Termination {
    let mut registry = Registry::default();

    for i in 0..10000usize {
        registry
            .commands()
            .spawn((TestData1 { s: i as u32 }, TestData2 { s: i as u32 }));
    }
    for i in 0..10000usize {
        registry.commands().spawn((
            TestData1 { s: i as u32 },
            TestData2 { s: i as u32 },
            TestData3 { s: i as u32 },
        ));
    }
    for i in 0..10000usize {
        registry.commands().spawn((
            TestData1 { s: i as u32 },
            TestData3 { s: i as u32 },
            TestData4 { s: i as u32 },
        ));
    }
    for i in 0..10000usize {
        registry.commands().spawn((
            TestData1 { s: i as u32 },
            TestData2 { s: i as u32 },
            TestData3 { s: i as u32 },
            TestData4 { s: i as u32 },
        ));
    }

    registry.flush_commands();
    dbg!(TestData2::id(), TestData3::id(), TestData4::id());
    let mut schedule = Schedule::new(7, &mut registry);
    schedule.add(move |query1: Query<(&mut TestData3, &mut TestData4)>| {
        for (a, b) in query1 {
            a.s += 1;
            dbg!(a);
        }
    });
    schedule.add(move |query1: Query<(&mut TestData3, &mut TestData4), (Without<TestData2>, Superset)>| {
        for (a, b) in query1 {
            a.s += 1;
            dbg!(a);
        }

    });

    bencher.iter(|| {
        schedule.execute();
    });
    drop(schedule);

}
