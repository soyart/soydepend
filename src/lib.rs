#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

type Edges<T> = HashMap<T, HashSet<T>>;

#[derive(Default, Debug)]
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
    T: Clone + Eq + std::hash::Hash + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            nodes: HashSet::default(),
            dependents: HashMap::default(),
            dependencies: HashMap::default(),
        }
    }

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

    #[inline(always)]
    pub fn depends_on_directly(&self, dependent: &T, dependency: &T) -> bool {
        self.dependencies
            .get(dependent)
            .map(|deps| deps.contains(dependency))
            .unwrap_or(false)
    }

    pub fn dependencies(&self, node: &T) -> HashSet<T> {
        dig_deep(&self.dependencies, node)
    }

    pub fn dependents(&self, node: &T) -> HashSet<T> {
        dig_deep(&self.dependents, node)
    }

    pub fn depends_on(&self, dependent: &T, dependency: &T) -> bool {
        self.dependencies(dependent).contains(dependency)
    }
}

fn insert_to_deps<T>(edges: &mut HashMap<T, HashSet<T>>, key: T, value: T)
where
    T: Clone + Eq + std::hash::Hash + std::fmt::Debug,
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
    T: Clone + Eq + std::hash::Hash + std::fmt::Debug,
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
    T: Clone + Eq + std::hash::Hash + std::fmt::Debug,
{
    let nodes = edges.get_mut(key);
    if nodes.is_none() {
        return;
    }

    let nodes = nodes.unwrap();
    if !nodes.contains(target) {
        return;
    }

    if nodes.len() <= 1 {
        edges.remove(key);
        return;
    }

    nodes.remove(target);
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

    const BIGBANG: &'static str = "bigbang";
    const STAR_DUST: &'static str = "stardust";
    const STAR: &'static str = "star";
    const PROTO_PLANET: &'static str = "proto-planet";
    const PLANET: &'static str = "planet";

    fn default_graph<'a>() -> Graph<&'a str> {
        let mut g = Graph::<&str>::default();
        g.depend(STAR_DUST, BIGBANG).unwrap();
        g.depend(STAR, STAR_DUST).unwrap();
        g.depend(PROTO_PLANET, STAR).unwrap();
        g.depend(PLANET, PROTO_PLANET).unwrap();

        g
    }

    #[test]
    fn test_basic_dependency() {
        let mut g = default_graph();
        assert_eq!(g.dependents(&STAR), HashSet::from([PROTO_PLANET, PLANET]));

        assert_eq!(true, g.depends_on(&STAR, &STAR_DUST));
        assert_eq!(true, g.depends_on(&STAR, &BIGBANG));
        assert_eq!(true, g.depends_on(&STAR_DUST, &BIGBANG));
        assert_eq!(false, g.depends_on(&BIGBANG, &STAR_DUST));

        assert_eq!(true, g.depends_on(&PLANET, &BIGBANG));
        assert_eq!(true, g.depends_on(&PLANET, &STAR_DUST));
        assert_eq!(true, g.depends_on(&PLANET, &STAR));
        assert_eq!(true, g.depends_on(&PLANET, &PROTO_PLANET));

        assert_eq!(true, g.depends_on(&PROTO_PLANET, &BIGBANG));
        assert_eq!(true, g.depends_on(&PROTO_PLANET, &STAR_DUST));
        assert_eq!(true, g.depends_on(&PROTO_PLANET, &STAR));

        assert_eq!(true, g.depends_on(&STAR, &BIGBANG));
        assert_eq!(true, g.depends_on(&STAR, &STAR_DUST));

        assert_eq!(true, g.depends_on(&STAR_DUST, &BIGBANG));

        assert_eq!(false, g.depends_on(&BIGBANG, &PLANET));
        assert_eq!(false, g.depends_on(&STAR_DUST, &PLANET));
        assert_eq!(false, g.depends_on(&STAR, &PLANET));
        assert_eq!(false, g.depends_on(&PROTO_PLANET, &PLANET));
        assert_eq!(false, g.depends_on(&PLANET, &PLANET));

        assert_eq!(false, g.depends_on(&BIGBANG, &PROTO_PLANET));
        assert_eq!(false, g.depends_on(&STAR_DUST, &PROTO_PLANET));
        assert_eq!(false, g.depends_on(&STAR, &PROTO_PLANET));
        assert_eq!(false, g.depends_on(&PROTO_PLANET, &PROTO_PLANET));

        assert_eq!(false, g.depends_on(&BIGBANG, &STAR));
        assert_eq!(false, g.depends_on(&STAR_DUST, &STAR));
        assert_eq!(false, g.depends_on(&STAR, &STAR));

        assert_eq!(false, g.depends_on(&BIGBANG, &STAR_DUST));
        assert_eq!(false, g.depends_on(&STAR_DUST, &STAR_DUST));

        g.depend(STAR_DUST, STAR)
            .expect_err("stardust should not depend on star");

        g.depend(BIGBANG, "god").unwrap();
        g.depend("sun", STAR_DUST).unwrap();
        g.depend("earth", "sun").unwrap();
        g.depend("human", "earth").unwrap();

        assert_eq!(true, g.depends_on(&"human", &"earth"));
        assert_eq!(true, g.depends_on(&"human", &"sun"));
        assert_eq!(true, g.depends_on(&"human", &STAR_DUST));
        assert_eq!(true, g.depends_on(&"human", &"god"));
    }

    #[test]
    fn test_depends_on_directly() {
        let mut g = Graph::new();

        g.depend("b", "a").unwrap();
        g.depend("c", "b").unwrap();
        g.depend("d", "c").unwrap();

        assert_eq!(true, g.depends_on_directly(&"d", &"c"));
        assert_eq!(true, g.depends_on_directly(&"c", &"b"));
        assert_eq!(true, g.depends_on_directly(&"b", &"a"));

        assert_eq!(false, g.depends_on_directly(&"d", &"b"));
        assert_eq!(false, g.depends_on_directly(&"c", &"a"));
        assert_eq!(false, g.depends_on_directly(&"b", &"x"));
    }

    #[test]
    fn test_deep_dig() {
        let mut g = default_graph();

        assert_eq!(
            g.dependents(&BIGBANG), //
            HashSet::from([STAR, STAR_DUST, PROTO_PLANET, PLANET])
        );

        assert_eq!(
            g.dependencies(&BIGBANG), //
            HashSet::default(),
        );

        assert_eq!(
            g.dependencies(&STAR_DUST), //
            HashSet::from([BIGBANG]),
        );

        assert_eq!(
            g.dependencies(&STAR), //
            HashSet::from([BIGBANG, STAR_DUST]),
        );

        assert_eq!(
            g.dependencies(&PLANET), //
            HashSet::from([BIGBANG, STAR_DUST, STAR, PROTO_PLANET]),
        );

        g.depend(BIGBANG, "god").unwrap();
        g.depend("sun", STAR_DUST).unwrap();
        g.depend("earth", "sun").unwrap();
        g.depend("earth", "god").unwrap();
        g.depend("human", "earth").unwrap();

        {
            assert_eq!(
                g.dependents(&"god"),
                HashSet::from([
                    BIGBANG,
                    STAR_DUST,
                    STAR,
                    PROTO_PLANET,
                    PLANET,
                    "sun",
                    "earth",
                    "human"
                ]),
            );

            assert_eq!(
                g.dependents(&BIGBANG),
                HashSet::from([
                    STAR_DUST,
                    STAR,
                    PROTO_PLANET,
                    PLANET,
                    "sun",
                    "earth",
                    "human"
                ])
            );

            assert_eq!(
                g.dependents(&STAR_DUST),
                HashSet::from([STAR, PROTO_PLANET, PLANET, "sun", "earth", "human"])
            );

            assert_eq!(g.dependents(&STAR), HashSet::from([PROTO_PLANET, PLANET]));
        }

        {
            assert_eq!(g.dependencies(&"god"), HashSet::default());

            assert_eq!(
                g.dependencies(&"sun"),
                HashSet::from([STAR_DUST, BIGBANG, "god"])
            );

            assert_eq!(
                g.dependencies(&"earth"),
                HashSet::from([STAR_DUST, BIGBANG, "god", "sun"])
            );

            assert_eq!(
                g.dependencies(&"human"),
                HashSet::from(["god", BIGBANG, STAR_DUST, "sun", "earth"])
            );

            g.depend("human", PLANET).unwrap();
            assert_eq!(
                g.dependencies(&"human"),
                HashSet::from([
                    "god",
                    BIGBANG,
                    STAR_DUST,
                    "sun",
                    "earth",
                    STAR,
                    PROTO_PLANET,
                    PLANET
                ])
            );
        }
    }

    #[test]
    fn test_undepend() {
        let mut g = Graph::<&str>::default();
        g.depend(STAR_DUST, BIGBANG).unwrap();
        g.depend(STAR, STAR_DUST).unwrap();

        g.undepend(&STAR, &BIGBANG)
            .expect_err("should not be able to undepend deep dependency");

        g.undepend(&STAR, &STAR_DUST)
            .expect("should be able to undepend direct dependency");

        assert_eq!(false, g.depends_on(&STAR, &STAR_DUST));
        assert_eq!(false, g.depends_on(&STAR, &BIGBANG));
    }
}
