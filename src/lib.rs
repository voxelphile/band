//Hello, band!
#![allow(dead_code)]
#![feature(return_position_impl_trait_in_trait, fn_traits)]

use core::slice;
use crossbeam::channel::*;
use derive_more::*;
use std::{
    any::{type_name, TypeId},
    arch,
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    iter,
    marker::PhantomData,
    mem, ptr,
    time::{Instant, Duration}, hint::black_box, error::Error, thread::{JoinHandle, self}, convert::identity,
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

pub enum Access {
    Ref(DataId),
    Mut(DataId),
}

impl Access {
    fn overlaps(&self, other: &Self) -> bool {
        use Access::*;
        match (self, other) {
            (Ref(_), Ref(_)) => false,
            (Ref(x), Mut(y)) |
            (Mut(x), Ref(y)) |
            (Mut(x), Mut(y)) => x == y,
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

pub trait Bundle: Into<Vec<ComponentPack>> {}

impl<T: Into<Vec<ComponentPack>>> Bundle for T {}

pub enum Command {
    Spawn(Vec<ComponentPack>),
    Insert(Entity, Vec<ComponentPack>),
}

pub struct Commands {
    tx: Sender<Command>,
}

impl Commands {
    fn spawn(&self, bundle: impl Bundle) {
        self.tx.send(Command::Spawn(bundle.into()));
    }
    fn insert(&self, entity: Entity, bundle: impl Bundle) {
        self.tx.send(Command::Insert(entity, bundle.into()));
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
    fn insert(&mut self, entity: Entity, bundle: Vec<ComponentPack>) {
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

        for ComponentPack(info, boxed_component) in bundle {
            let DataInfo { id, .. } = info;
            let position = archetype.iter().position(|probe| *probe == id).unwrap();

            let index = archetype.translations(&self.data_info)[position];

            data.splice(index..index, unsafe {
                boxed_component.as_raw().iter().copied()
            });

            table.insert(position, boxed_component);
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

pub struct Query<'a, Q: Queryable> {
    storage: Vec<(Archetype, Storage, Vec<usize>)>,
    tx: Sender<(Archetype, Storage)>,
    marker: PhantomData<&'a mut Q>,
}

impl<'a, Q: Queryable> Drop for Query<'a, Q> {
    fn drop(&mut self) {
        for pair in self.storage.drain(..).map(|(x, y, _)| (x, y)) {
            self.tx.send(pair).expect("failed to return storage");
        }
    }
}

impl<'a, Q: Queryable> IntoIterator for Query<'a, Q> {
    type Item = Q;
    type IntoIter = QueryIter<'a, Q>;
    fn into_iter(self) -> Self::IntoIter {
        QueryIter {
            query: self,
            inner: 0,
            outer: 0,
        }
    }
}

pub struct QueryIter<'a, Q: Queryable> {
    query: Query<'a, Q>,
    inner: usize,
    outer: usize,
}

pub trait Queryable: DataExt + Send + Sync + 'static {
    type Target: DataExt;
    fn access(access: &mut Vec<Access>);
    fn archetype(archetype: &mut Archetype) {
        let position = archetype.ordered_position(&Self::Target::id());
        archetype.insert(position, Self::Target::id());
    }
    fn order(archetype: &Archetype, order: &mut Vec<usize>) {
        order.push(
            archetype
                .iter()
                .position(|probe| probe == &Self::Target::id())
                .unwrap(),
        )
    }
    fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
    where
        Self: Sized;
}

pub trait QueryableExt<'a, 'b: 'a>: Queryable {
    fn query(registry: &'b mut Registry) -> Query<'a, Self>
    where
        Self: Sized,
    {
        registry.return_storage();

        let mut query_archetype = Default::default();
        Self::archetype(&mut query_archetype);

        let mut storage_archetypes = vec![];
        for storage_archetype in registry.storage.keys() {
            if storage_archetype.is_superset(&query_archetype) {
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
}

impl<'a, 'b: 'a, Q: Queryable> QueryableExt<'a, 'b> for Q {}

impl<'a, Q: Queryable> Iterator for QueryIter<'a, Q> {
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

#[derive(Debug, PartialEq)]
pub struct TestData1 {
    s: u32,
}
impl Data for TestData1 {}
impl Component for TestData1 {}
#[derive(Debug, PartialEq)]
pub struct TestData2 {
    s: u32,
}
impl Data for TestData2 {}
impl Component for TestData2 {}
#[derive(Debug, PartialEq)]
pub struct TestData3 {
    s: u32,
}
impl Data for TestData3 {}
impl Component for TestData3 {}
#[derive(Debug, PartialEq)]
pub struct TestData4 {
    s: u32,
}
impl Data for TestData4 {}
impl Component for TestData4 {}
#[derive(Debug, PartialEq)]
pub struct TestData5 {
    s: u32,
}
impl Data for TestData5 {}
impl Component for TestData5 {}

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
impl<A: Data, B: Data> Data for (A, B) {}
impl<A: Queryable, B: Queryable> Queryable for (A, B) {
    type Target = (A, B);
    fn access(access: &mut Vec<Access>) {
        A::access(access);
        B::access(access);
    }
    fn archetype(archetype: &mut Archetype) {
        A::archetype(archetype);
        B::archetype(archetype);
    }
    fn order(archetype: &Archetype, order: &mut Vec<usize>) {
        A::order(archetype, order);
        B::order(archetype, order);
    }
    fn get(ptr: *mut u8, translations: &[usize], idx: &mut usize) -> Self
    where
        Self: Sized,
    {
        (
            A::get(ptr, translations, idx),
            B::get(ptr, translations, idx),
        )
    }
}

pub struct SystemQuery<Q: Queryable> {
    marker: PhantomData<Q>,
}

pub trait SystemIn<'a, 'b: 'a> where Self: 'b + Send {
    fn prepare_execution(registry: &'a mut Registry) -> Self;
    fn access(access: &mut Vec<Access>);
}

impl<'a, 'b: 'a> SystemIn<'a, 'b> for () {
    fn prepare_execution(registry: &mut Registry) -> Self {
        ()
    }
    fn access(access: &mut Vec<Access>) {}
}

macro_rules! impl_system_in {
    ($($items:ident),*) => {
    #[allow(unused_parens)] // This is added because the nightly compiler complains
        impl<'a, 'b: 'a, 'c: 'b, $($items: SystemIn<'a, 'b>),*> SystemIn<'a, 'b> for ($($items),*,)
        {
            fn prepare_execution(registry: &'a mut Registry) -> Self {
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

pub trait SystemOut where Self: Send {
    fn handle(self, name: &str);
}

impl SystemOut for () {
    fn handle(self, _: &str) {}
}

impl<E: Error + Send> SystemOut for Result<(), E> {
    fn handle(self, name: &str) {
        self.expect(&format!("System `{name}` failed to execute"))
    }
} 

pub trait System<'a, 'b: 'a, In: SystemIn<'a, 'b>, Out: SystemOut>: Send {
    fn prepare_execution(&self, registry: &'a mut Registry) -> In;
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
        impl<'a, 'b: 'a, $($x: SystemIn<'a, 'b>,)* Return: SystemOut, Function: ::std::ops::Fn($($y,)*) -> Return + Send> System<'a, 'b, ($($x,)*), Return> for Function {
            fn prepare_execution(&self, registry: &'a mut Registry) -> ($($x),*,) {
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

impl<Q: Queryable> SystemParam for SystemQuery<Q> {
    type In = Query<'static, Q>;
}
impl<'a, 'b: 'a, Q: Queryable> SystemIn<'a, 'b> for Query<'b, Q> {
    fn prepare_execution(registry: &'a mut Registry) -> Self {
        Q::query(registry)
    }
    fn access(access: &mut Vec<Access>) {
        Q::access(access)
    }
}

pub struct SystemBuilder<A: Flatten> {
    param: A,
    name: String,
}

impl SystemBuilder<()> {
    fn new() -> SystemBuilder<()> {
        Self { param: (), name: "unnamed".to_string() }
    }
}

impl<A: Flatten> SystemBuilder<A> {
    fn with_name(self, name: impl ToString) -> Self {
        Self {
            name: name.to_string(),
            ..self
        }
    }

    fn with_query<Q: Queryable>(self) -> SystemBuilder<(SystemQuery<Q>, A)>
    where
        (SystemQuery<Q>, A): Flatten,
    {
        SystemBuilder::<(SystemQuery<Q>, A)> {
            param: (
                SystemQuery {
                    marker: PhantomData,
                },
                self.param,
            ),
            name: self.name
        }
    }

    fn build<'a, 'b: 'a, R: SystemOut>(
        self,
        system: impl System<'a, 'b, <A::Output as SystemParam>::In, R> + 'static,
    ) -> impl Schedulable<'a, 'b>
    where
        A::Output: SystemParam,
        <A::Output as SystemParam>::In: SystemIn<'a, 'b> + 'a,
        R: 'a
    {
        SystemSchedulable {
            system: Box::new(system),
            input: None,
            name: self.name
        }
    }
}

pub struct SystemSchedulable<'a, 'b: 'a, In: SystemIn<'a, 'b> + 'a, Out: SystemOut + 'a> {
    system: Box<dyn System<'a, 'b, In, Out>>,
    input: Option<In>,
    name: String,
}

impl<'a, 'b: 'a, In: SystemIn<'a, 'b>, Out: SystemOut> Schedulable<'a, 'b> for SystemSchedulable<'a, 'b, In, Out> {
    fn prepare_execution(&mut self, registry: &mut Registry) {
        self.input = Some(self.system.prepare_execution(registry));
    }
    fn execute(&mut self) {
        self.system.execute(self.input.take().unwrap()).handle(&self.name);
    }
    fn access(&self) -> Vec<Access> {
        let mut access = vec![];
        In::access(&mut access);
        access
    }
}

pub trait Schedulable<'a, 'b: 'a>: 'a + Send {
    fn prepare_execution(&mut self, registry: &'b mut Registry);
    fn execute(&mut self);
    fn access(&self) -> Vec<Access>;
}

pub type NodeId = usize;

#[derive(Default)]
pub struct Graph<'a, 'b: 'a> {
    nodes: Vec<Box<dyn Schedulable<'a, 'b>>>,
    dependencies: Vec<Vec<NodeId>>,
}

impl<'a, 'b: 'a> Graph<'a, 'b> {
    fn add(&mut self, schedulable: impl Schedulable<'a, 'b>) {
        let my_id = self.nodes.len();

        let access = schedulable.access();

        self.nodes.push(Box::new(schedulable));

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

pub type NodePayload<'a, 'b: 'a> = (NodeId, Box<dyn Schedulable<'a, 'b>>);

pub struct Schedule<'a, 'b: 'a> {
    graph: Graph<'a, 'b>,
    work_tx: Sender<NodePayload<'a, 'b>>,
    done_rx: Receiver<NodePayload<'a, 'b>>,
    workers: Vec<JoinHandle<()>>,
}
impl<'a, 'b: 'a> Schedule<'a, 'b> {
    fn new(workers: usize) {
        let (work_tx, work_rx) = bounded::<NodePayload>(8192);
        let (done_tx, done_rx) = bounded::<NodeId>(8192);
        let workers = (0..workers)
            .into_iter()
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
                            .send(id)
                            .expect("failed to signal work unit as done");
                    })
                    .expect("failed to start worker")
            })
            .collect::<Vec<_>>();
    }
    fn add(&mut self, schedulable: impl Schedulable<'a, 'b>) {
        self.graph.add(schedulable);
    }
    fn execute(&mut self) {
        let mut executing = Vec::new();

        let not_executed = self.graph.nodes.drain(..).collect::<VecDeque<_>>();
        let mut executed = (0..not_executed.len()).map(|_| None).collect::<Vec<_>>();
        
        let mut nodes_iter = not_executed.into_iter().enumerate().peekable();

        loop {
            let Some((id, node)) = nodes_iter.next() else {
                break;
            };

            loop {
                if executing
                            .iter()
                            .any(|id| self.graph.dependencies[nodes_iter.peek().unwrap().0].contains(id))
                {
                    break;
                }
                while let Ok((id, schedulable)) = self.done_rx.try_recv() {
                    executing.remove(id);
                    executed[id] = Some(schedulable);
                }
            }

            executing.push(id);

            self.work_tx
                .try_send((id, node))
                .expect("failed to send work unit");
        }

        self.graph.nodes = executed.into_iter().filter_map(identity).collect();
    }
}

#[test]
fn graph_works() {
    let mut registry = Registry::default();
    let mut a = vec![10; 60000];
    let i = std::time::Instant::now();
    for i in 0..30000 {
        let a1 = a[2 * i];
        let b1 = a[2 * i + 1];
        a[2 * i] = b1;
        a[2 * i + 1] = a1;
    }
    println!("{:?}", std::time::Instant::now().duration_since(i) / 30000);
    for i in 0..10000usize {
        let e = registry.spawn();
        registry.insert(
            e,
            vec![ComponentPack(
                TestData1::info(),
                Box::new(TestData1 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData2::info(),
                Box::new(TestData2 { s: i as u32 }),
            )],
        );
    }
    for i in 0..10000usize {
        let e = registry.spawn();
        registry.insert(
            e,
            vec![ComponentPack(
                TestData1::info(),
                Box::new(TestData1 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData2::info(),
                Box::new(TestData2 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData3::info(),
                Box::new(TestData3 { s: i as u32 }),
            )],
        );
    }
    for i in 0..10000usize {
        let e = registry.spawn();
        registry.insert(
            e,
            vec![ComponentPack(
                TestData1::info(),
                Box::new(TestData1 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData2::info(),
                Box::new(TestData2 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData3::info(),
                Box::new(TestData3 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData4::info(),
                Box::new(TestData4 { s: i as u32 }),
            )],
        );
    }
    for i in 0..10000usize {
        let e = registry.spawn();
        registry.insert(
            e,
            vec![ComponentPack(
                TestData1::info(),
                Box::new(TestData1 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData2::info(),
                Box::new(TestData2 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData3::info(),
                Box::new(TestData3 { s: i as u32 }),
            )],
        );
        registry.insert(
            e,
            vec![ComponentPack(
                TestData5::info(),
                Box::new(TestData5 { s: i as u32 }),
            )],
        );
    }
    // async fn first_system(e: Entity, d: &mut TestData, t: &mut TestData2) {
    //     mem::swap(&mut d.s, &mut t.s);
    // }
    // async fn second_system(e: Entity, d: &mut TestData3, t: &mut TestData4) {
    //     mem::swap(&mut d.s, &mut t.s);
    // }
    // async fn third_system(e: Entity, d: &mut TestData3, t: &mut TestData5) {
    //     mem::swap(&mut d.s, &mut t.s);
    // }
    let i = std::time::Instant::now();
    for (d, t) in <(&mut TestData1, &mut TestData2)>::query(&mut registry) {
        mem::swap(&mut d.s, &mut t.s);
    }
    for (d, t) in <(&mut TestData3, &mut TestData4)>::query(&mut registry) {
        mem::swap(&mut d.s, &mut t.s);
    }
    for (d, t) in <(&mut TestData3, &mut TestData5)>::query(&mut registry) {
        mem::swap(&mut d.s, &mut t.s);
    }
    println!("{:?}", std::time::Instant::now().duration_since(i) / 60000);

    let mut schedule = Schedule::default();
    schedule.add(
        SystemBuilder::new()
            .with_name("test")
            .with_query::<(&mut TestData1, &mut TestData2)>()
            .build(|query1| {
                
            }),
    );
}
