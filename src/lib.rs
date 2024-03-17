use std::collections::{HashMap, HashSet};

type Edges<T> = HashMap<T, HashSet<T>>;

#[derive(Clone, Default, Debug)]
pub struct Graph<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    pub(crate) nodes: HashSet<T>,
    pub(crate) dependents: Edges<T>,
    pub(crate) dependencies: Edges<T>,
}

#[derive(Debug)]
pub enum Error {
    CircularDependency,
    DependencyExists,
    DependsOnSelf,
    NoSuchDirectDependency,
    NoSuchNode,
}

impl<T> Graph<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    pub fn new() -> Self {
        Self {
            nodes: HashSet::default(),
            dependents: HashMap::default(),
            dependencies: HashMap::default(),
        }
    }

    /// Add dependency edges to the graph
    pub fn depend(&mut self, dependent: T, dependency: T) -> Result<(), Error> {
        if dependent == dependency {
            return Err(Error::DependsOnSelf);
        }

        if self.depends_on(&dependency, &dependent) {
            return Err(Error::CircularDependency);
        }

        self.nodes.insert(dependent.clone());
        self.nodes.insert(dependency.clone());

        insert_to_deps(&mut self.dependents, dependency.clone(), dependent.clone());
        insert_to_deps(&mut self.dependencies, dependent, dependency);

        Ok(())
    }

    /// Removes dependency edges from the graph
    pub fn undepend(&mut self, dependent: &T, dependency: &T) -> Result<(), Error> {
        if !self.depends_on_directly(dependent, dependency) {
            return Err(Error::NoSuchDirectDependency);
        }

        rm_from_deps(&mut self.dependencies, dependent, dependency);
        rm_from_deps(&mut self.dependents, dependency, dependent);

        Ok(())
    }

    #[inline(always)]
    pub fn contains(&self, node: &T) -> bool {
        self.nodes.contains(node)
    }

    /// Returns whether dependent depends directly on dependency
    #[inline(always)]
    pub fn depends_on_directly(&self, dependent: &T, dependency: &T) -> bool {
        edges_contain(&self.dependencies, dependent, dependency)
    }

    /// Returns deep dependencies of node
    pub fn dependencies(&self, node: &T) -> HashSet<T> {
        dig_deep(&self.dependencies, node)
    }

    /// Returns deep dependents of node
    pub fn dependents(&self, node: &T) -> HashSet<T> {
        dig_deep(&self.dependents, node)
    }

    /// Returns whether dependent depends on dependency in some way
    pub fn depends_on(&self, dependent: &T, dependency: &T) -> bool {
        self.dependencies(dependent).contains(dependency)
    }

    /// Returns whether the node is depended on by other
    pub fn is_dependend(&self, node: &T) -> bool {
        self.dependents
            .get(node)
            .is_some_and(|deps| !deps.is_empty())
    }

    pub fn leaves(&self) -> HashSet<T> {
        let mut leaves = HashSet::new();

        for n in &self.nodes {
            if !self.dependencies.contains_key(n) {
                leaves.insert(n.clone());
            }
        }

        leaves
    }

    pub fn layers(&self) -> Vec<HashSet<T>> {
        let mut layers = Vec::new();
        let mut cloned = self.clone();

        while !cloned.nodes.is_empty() {
            let leaves = cloned.leaves();
            layers.push(leaves.clone());

            leaves.iter().for_each(|leaf| cloned.delete(leaf));
        }

        layers
    }

    /// Internal method for complete removal of the target
    fn delete(&mut self, target: &T) {
        if let Some(dependencies) = self.dependencies.get(target) {
            dependencies
                .iter()
                .for_each(|dependency| rm_from_deps(&mut self.dependents, dependency, target));
        }

        if let Some(dependents) = self.dependents.get(target) {
            dependents
                .iter()
                .for_each(|dependent| rm_from_deps(&mut self.dependencies, dependent, target));
        }

        self.dependencies.remove(target);
        self.dependents.remove(target);
        self.nodes.remove(target);
    }

    /// Removes undepended target node
    pub fn remove(&mut self, target: &T) -> Result<(), Error> {
        if !self.contains(target) {
            return Err(Error::NoSuchNode);
        }

        if self.is_dependend(target) {
            return Err(Error::DependencyExists);
        }

        self.delete(target);
        Ok(())
    }

    fn remove_deep(&mut self, target: &T, remove_dependencies: bool) {
        let mut q = vec![target.clone()];

        while !q.is_empty() {
            let current = pop_queue(&mut q);

            // Check before clone
            if self.dependents.contains_key(&current) {
                self.dependents
                    .clone()
                    .get(&current)
                    .unwrap()
                    .iter()
                    .for_each(|dependent| {
                        self.undepend(dependent, &current).unwrap();
                        q.push(dependent.clone());
                    });
            }

            // Check before clone
            if self.dependencies.contains_key(&current) {
                for dependency in self.dependencies.clone().get(&current).unwrap() {
                    // Push dependency to queue if remove_dependencies is set,
                    // and the dependency only has 1 dependent which happens to be current
                    if remove_dependencies {
                        if let Some(siblings) = self.dependents.get(dependency) {
                            assert!(!siblings.is_empty());
                            assert!(siblings.contains(&current));

                            if siblings.len() != 1 {
                                continue;
                            }
                        }

                        q.push(dependency.clone());
                    }

                    self.undepend(&current, dependency).unwrap();
                }
            }

            self.delete(&current);
        }
    }

    pub fn remove_force(&mut self, target: &T) {
        self.remove_deep(target, false);
    }

    pub fn remove_autoremove(&mut self, target: &T) {
        self.remove_deep(target, true);
    }

    /// Shrinks graph to minimal memory allocation,
    /// while keeping values intact.
    pub fn realloc(&mut self) {
        self.nodes.shrink_to_fit();
        self.dependents.shrink_to_fit();
        self.dependencies.shrink_to_fit();
    }
}

/// Asserts that invariants are still valid
pub fn assert_no_dangling<T>(g: &Graph<T>)
where
    T: Clone + std::fmt::Debug + std::hash::Hash + Eq,
{
    for (dependency, dependents) in &g.dependents {
        assert!(g.nodes.contains(dependency));

        dependents.iter().for_each(|dependent| {
            assert!(g.nodes.contains(dependent));
            assert!(edges_contain(&g.dependents, dependency, dependent));
            assert!(edges_contain(&g.dependencies, dependent, dependency));
        });
    }

    for (dependent, dependencies) in &g.dependencies {
        assert!(g.nodes.contains(dependent));

        dependencies.iter().for_each(|dependency| {
            assert!(g.nodes.contains(dependent));
            assert!(edges_contain(&g.dependents, dependency, dependent));
            assert!(edges_contain(&g.dependencies, dependent, dependency));
        })
    }
}

fn insert_to_deps<T>(edges: &mut HashMap<T, HashSet<T>>, key: T, value: T)
where
    T: Clone + Eq + std::hash::Hash,
{
    match edges.get_mut(&key) {
        Some(set) => {
            set.insert(value);
        }
        None => {
            edges.insert(key, HashSet::from([value]));
        }
    };
}

#[inline(always)]
fn dig_deep<T>(edges: &HashMap<T, HashSet<T>>, node: &T) -> HashSet<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    let mut search_next = vec![node];
    let mut result = HashSet::<T>::new();

    while !search_next.is_empty() {
        let mut discovered = Vec::new();

        for next in search_next.iter() {
            let nodes = edges.get(next);
            if nodes.is_none() {
                continue;
            }

            for n in nodes.unwrap() {
                if result.contains(n) {
                    continue;
                }

                discovered.push(n);
                result.insert(n.clone());
            }
        }

        search_next = discovered;
    }

    result
}

fn rm_from_deps<T>(edges: &mut Edges<T>, key: &T, target: &T)
where
    T: Clone + Eq + std::hash::Hash,
{
    let nodes = edges.get_mut(key);
    if nodes.is_none() {
        return;
    }

    let nodes = nodes.unwrap();
    if !nodes.contains(target) {
        return;
    }

    if nodes.len() != 1 {
        nodes.remove(target);
        return;
    }

    edges.remove(key);
}

fn pop_queue<T>(queue: &mut Vec<T>) -> T
where
    T: Clone,
{
    assert!(!queue.is_empty());

    let popped = queue[0].clone();
    queue.remove(0);

    popped
}

fn edges_contain<T>(edges: &Edges<T>, key: &T, value: &T) -> bool
where
    T: Eq + std::hash::Hash,
{
    edges.get(key).is_some_and(|values| values.contains(value))
}

#[test]
fn test_pop_queue() {
    let mut q = vec![0, 1, 2, 3, 4, 5, 20, 17];
    for v in q.clone().into_iter() {
        assert_eq!(v, pop_queue(&mut q));
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircularDependency => write!(f, "circular dependency"),
            Self::DependencyExists => write!(f, "dependencies exist"),
            Self::DependsOnSelf => write!(f, "depends on self"),
            Self::NoSuchDirectDependency => write!(f, "no such direct dependency relationship"),
            Self::NoSuchNode => write!(f, "no such node"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! set {
        ($($x:expr),*) => {
            HashSet::from([$($x), *])
        };

        [$($x:expr),*] => {
            new_set!($($x), *)
        };
    }

    const BIGBANG: &'static str = "bigbang";
    const STARDUST: &'static str = "stardust";
    const STAR: &'static str = "star";
    const PROTO_PLANET: &'static str = "proto-planet";
    const PLANET: &'static str = "planet";

    fn default_graph<'a>() -> Graph<&'a str> {
        let mut g = Graph::<&str>::default();
        g.depend(STARDUST, BIGBANG).unwrap();
        g.depend(STAR, STARDUST).unwrap();
        g.depend(PROTO_PLANET, STAR).unwrap();
        g.depend(PLANET, PROTO_PLANET).unwrap();

        assert_no_dangling(&g);
        g
    }

    #[test]
    fn test_basic_dependency() {
        let mut g = default_graph();
        assert_eq!(g.dependents(&STAR), set![PROTO_PLANET, PLANET]);
        assert_eq!(g.dependents(&STAR), set!(PROTO_PLANET, PLANET));

        assert!(g.depends_on(&STAR, &STARDUST));
        assert!(g.depends_on(&STAR, &BIGBANG));
        assert!(g.depends_on(&STARDUST, &BIGBANG));

        assert!(g.depends_on(&PLANET, &BIGBANG));
        assert!(g.depends_on(&PLANET, &STARDUST));
        assert!(g.depends_on(&PLANET, &STAR));
        assert!(g.depends_on(&PLANET, &PROTO_PLANET));

        assert!(g.depends_on(&PROTO_PLANET, &BIGBANG));
        assert!(g.depends_on(&PROTO_PLANET, &STARDUST));
        assert!(g.depends_on(&PROTO_PLANET, &STAR));

        assert!(g.depends_on(&STAR, &BIGBANG));
        assert!(g.depends_on(&STAR, &STARDUST));

        assert!(g.depends_on(&STARDUST, &BIGBANG));

        assert!(!g.depends_on(&BIGBANG, &STARDUST));
        assert!(!g.depends_on(&BIGBANG, &PLANET));
        assert!(!g.depends_on(&STARDUST, &PLANET));
        assert!(!g.depends_on(&STAR, &PLANET));
        assert!(!g.depends_on(&PROTO_PLANET, &PLANET));
        assert!(!g.depends_on(&PLANET, &PLANET));

        assert!(!g.depends_on(&BIGBANG, &PROTO_PLANET));
        assert!(!g.depends_on(&STARDUST, &PROTO_PLANET));
        assert!(!g.depends_on(&STAR, &PROTO_PLANET));
        assert!(!g.depends_on(&PROTO_PLANET, &PROTO_PLANET));

        assert!(!g.depends_on(&BIGBANG, &STAR));
        assert!(!g.depends_on(&STARDUST, &STAR));
        assert!(!g.depends_on(&STAR, &STAR));

        assert!(!g.depends_on(&BIGBANG, &STARDUST));
        assert!(!g.depends_on(&STARDUST, &STARDUST));

        g.depend(STARDUST, STAR)
            .expect_err("stardust should not depend on star");

        g.depend(BIGBANG, "god").unwrap();
        g.depend("sun", STARDUST).unwrap();
        g.depend("earth", "sun").unwrap();
        g.depend("human", "earth").unwrap();

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(g.depends_on(&"human", &"earth"));
        assert!(g.depends_on(&"human", &"sun"));
        assert!(g.depends_on(&"human", &STARDUST));
        assert!(g.depends_on(&"human", &"god"));
    }

    #[test]
    fn test_depends_on_directly() {
        let mut g = Graph::new();

        g.depend("b", "a").unwrap();
        g.depend("c", "b").unwrap();
        g.depend("d", "c").unwrap();

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(g.depends_on_directly(&"d", &"c"));
        assert!(g.depends_on_directly(&"c", &"b"));
        assert!(g.depends_on_directly(&"b", &"a"));

        assert!(!g.depends_on_directly(&"d", &"b"));
        assert!(!g.depends_on_directly(&"c", &"a"));
        assert!(!g.depends_on_directly(&"b", &"x"));
    }

    #[test]
    fn test_deep_dig() {
        let mut g = default_graph();

        assert_eq!(
            g.dependents(&BIGBANG), //
            set![STAR, STARDUST, PROTO_PLANET, PLANET]
        );
        assert_eq!(
            g.dependencies(&BIGBANG), //
            set![],
        );
        assert_eq!(
            g.dependencies(&STARDUST), //
            set![BIGBANG],
        );
        assert_eq!(
            g.dependencies(&STAR), //
            set![BIGBANG, STARDUST],
        );
        assert_eq!(
            g.dependencies(&PLANET), //
            set![BIGBANG, STARDUST, STAR, PROTO_PLANET]
        );

        g.depend(BIGBANG, "god").unwrap();
        g.depend("sun", STARDUST).unwrap();
        g.depend("earth", "sun").unwrap();
        g.depend("earth", "god").unwrap();
        g.depend("human", "earth").unwrap();

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        {
            assert_eq!(
                g.dependents(&"god"),
                set![
                    BIGBANG,
                    STARDUST,
                    STAR,
                    PROTO_PLANET,
                    PLANET,
                    "sun",
                    "earth",
                    "human"
                ],
            );

            assert_eq!(
                g.dependents(&BIGBANG),
                set![
                    STARDUST,
                    STAR,
                    PROTO_PLANET,
                    PLANET,
                    "sun",
                    "earth",
                    "human"
                ]
            );

            assert_eq!(
                g.dependents(&STARDUST),
                set![STAR, PROTO_PLANET, PLANET, "sun", "earth", "human"],
            );

            assert_eq!(
                g.dependents(&STAR), //
                set![PROTO_PLANET, PLANET],
            );
        }

        {
            assert_eq!(
                g.dependencies(&"god"), //
                set![]
            );
            assert_eq!(
                g.dependencies(&"sun"), //
                set![STARDUST, BIGBANG, "god"]
            );
            assert_eq!(
                g.dependencies(&"earth"), //
                set![STARDUST, BIGBANG, "god", "sun"],
            );

            assert_eq!(
                g.dependencies(&"human"),
                set!["god", BIGBANG, STARDUST, "sun", "earth"],
            );

            g.depend("human", PLANET).unwrap();

            assert_eq!(
                g.dependencies(&"human"),
                set![
                    "god",
                    BIGBANG,
                    STARDUST,
                    "sun",
                    "earth",
                    STAR,
                    PROTO_PLANET,
                    PLANET
                ],
            );
        }
    }

    #[test]
    fn test_undepend() {
        let mut g = Graph::<&str>::default();
        g.depend(STARDUST, BIGBANG).unwrap();
        g.depend(STAR, STARDUST).unwrap();

        g.undepend(&STAR, &BIGBANG)
            .expect_err("should not be able to undepend deep dependency");

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        g.undepend(&STAR, &STARDUST)
            .expect("should be able to undepend direct dependency");

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(!g.depends_on(&STAR, &STARDUST));
        assert!(!g.depends_on(&STAR, &BIGBANG));
    }

    #[test]
    fn test_delete() {
        let mut g = default_graph();

        g.delete(&PROTO_PLANET);
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        g.depend("b", "a").unwrap();
        g.depend("x", "a").unwrap();
        g.depend("y", "x").unwrap();
        g.depend("z", "y").unwrap();

        g.delete(&"y");
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        g.delete(&"a");
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        g.delete(&"x");
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test
    }

    #[test]
    fn test_leaves() {
        let mut g = default_graph();
        assert_eq!(g.leaves(), set![BIGBANG]);

        // a is the new leave
        g.depend("b", "a").unwrap();
        g.depend("x", "a").unwrap();
        g.depend("y", "x").unwrap();
        g.depend("z", "y").unwrap();
        assert_eq!(g.leaves(), set![BIGBANG, "a"]);

        // with y removed, z should be a leaf
        g.delete(&"y");
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert_eq!(g.leaves(), set![BIGBANG, "a", "z"]);
    }

    #[test]
    fn test_remove() {
        let mut g = default_graph();

        g.remove(&PROTO_PLANET)
            .expect_err("proto-planet is depended on by planet");

        assert_no_dangling(&g);

        g.remove(&PLANET).unwrap();

        assert_no_dangling(&g);

        assert_eq!(g.dependents(&BIGBANG), set![STARDUST, STAR, PROTO_PLANET]);
        assert!(!g.contains(&PLANET));
        assert!(!g.dependencies.contains_key(&PLANET));
        assert!(!g.dependents.contains_key(&PLANET));

        assert_eq!(g.dependencies(&PLANET), set![]);
        assert_eq!(g.dependents(&PLANET), set![]);

        assert_eq!(g.dependents(&PROTO_PLANET), set![]);
        assert_eq!(g.dependents(&STAR), set![PROTO_PLANET]);
        assert_eq!(g.dependents(&STARDUST), set![STAR, PROTO_PLANET]);
        assert_eq!(g.dependents(&BIGBANG), set![STARDUST, STAR, PROTO_PLANET]);

        assert_eq!(g.dependencies(&PROTO_PLANET), set![STAR, STARDUST, BIGBANG],);
        assert_eq!(g.dependencies(&STAR), set![STARDUST, BIGBANG]);
        assert_eq!(g.dependencies(&STARDUST), set![BIGBANG]);
        assert_eq!(g.dependencies(&BIGBANG), set![]);

        g.remove(&PROTO_PLANET).unwrap();
        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(!g.contains(&PROTO_PLANET));
        assert_eq!(g.dependencies(&PROTO_PLANET), set![]);
        assert_eq!(g.dependents(&PROTO_PLANET), set![]);

        assert_eq!(g.dependents(&STAR), set![]);
        assert_eq!(g.dependents(&STARDUST), set![STAR]);
        assert_eq!(g.dependents(&BIGBANG), set![STARDUST, STAR]);

        assert_eq!(g.dependencies(&STAR), set![STARDUST, BIGBANG]);
        assert_eq!(g.dependencies(&STARDUST), set![BIGBANG]);
        assert_eq!(g.dependencies(&BIGBANG), set![]);
    }

    #[test]
    fn test_remove_force() {
        let mut g = default_graph();
        g.remove_force(&STAR);

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(!g.contains(&STAR));
        assert!(!g.contains(&PROTO_PLANET));
        assert!(!g.contains(&PLANET));

        assert!(!g.dependents.contains_key(&STAR));
        assert!(!g.dependents.contains_key(&PROTO_PLANET));
        assert!(!g.dependents.contains_key(&PLANET));
        assert!(!g.dependencies.contains_key(&STAR));
        assert!(!g.dependencies.contains_key(&PROTO_PLANET));
        assert!(!g.dependencies.contains_key(&PLANET));

        assert_eq!(g.dependents(&BIGBANG), set![STARDUST]);
        assert_eq!(g.dependents(&STARDUST), set![]);
    }

    #[test]
    fn test_remove_autoremove() {
        let mut g = default_graph();
        g.depend("light", BIGBANG).unwrap();
        g.depend("uv", "light").unwrap();
        g.depend("infrared", "light").unwrap();
        g.depend("darkskin", "uv").unwrap();
        g.depend("blackhole", BIGBANG).unwrap();
        g.depend("whitehole", "blackhole").unwrap();

        g.remove_autoremove(&PROTO_PLANET);

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(!g.contains(&STARDUST));
        assert!(!g.contains(&STAR));
        assert!(!g.contains(&PROTO_PLANET));
        assert!(!g.contains(&PLANET));

        assert!(!g.dependents.contains_key(&STARDUST));
        assert!(!g.dependents.contains_key(&STAR));
        assert!(!g.dependents.contains_key(&PROTO_PLANET));
        assert!(!g.dependents.contains_key(&PLANET));
        assert!(!g.dependencies.contains_key(&STARDUST));
        assert!(!g.dependencies.contains_key(&STAR));
        assert!(!g.dependencies.contains_key(&PROTO_PLANET));
        assert!(!g.dependencies.contains_key(&PLANET));

        assert!(!g.depends_on(&"light", &"blackhole"));
        assert!(!g.depends_on(&"uv", &"blackhole"));
        assert!(!g.depends_on(&"infrared", &"blackhole"));
        assert!(!g.depends_on(&"light", &"whitehole"));
        assert!(!g.depends_on(&"uv", &"whitehole"));
        assert!(!g.depends_on(&"infrared", &"whitehole"));

        assert_eq!(
            g.dependents(&BIGBANG),
            set![
                "light",
                "infrared",
                "uv",
                "darkskin",
                "blackhole",
                "whitehole"
            ]
        );

        g.remove_autoremove(&"uv");

        g.realloc(); // random realloc test
        assert_no_dangling(&g); // random dangling test

        assert!(g.contains(&"light"));
        assert!(g.contains(&"infrared"));
        assert!(!g.contains(&"uv"));
        assert!(!g.contains(&"darkskin"));

        assert_eq!(
            g.dependents(&BIGBANG),
            set!["light", "infrared", "blackhole", "whitehole"]
        );
        assert_eq!(g.dependents(&"light"), set!["infrared"]);
        assert_eq!(g.dependents(&"infrared"), set![]);
        assert_eq!(g.dependents(&"blackhole"), set!["whitehole"]);
        assert_eq!(g.dependents(&"whitehole"), set![]);
        assert_eq!(g.dependencies(&BIGBANG), set![]);
        assert_eq!(g.dependencies(&"light"), set![BIGBANG]);
        assert_eq!(g.dependencies(&"infrared"), set![BIGBANG, "light"]);
        assert_eq!(g.dependencies(&"blackhole"), set![BIGBANG]);
        assert_eq!(g.dependencies(&"whitehole"), set![BIGBANG, "blackhole"],);
    }
}
