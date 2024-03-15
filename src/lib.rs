#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

pub trait Node: Clone + Eq + std::hash::Hash {}

#[allow(type_alias_bounds)]
type Edges<T: Node> = HashMap<T, HashSet<T>>;

#[derive(Default, Debug)]
pub struct Graph<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    nodes: HashSet<T>,
    dependents: Edges<T>,
    dependencies: Edges<T>,
}

pub enum ErrSoydeps {
    CircularDependency,
    DependenciesExists,
    DependsOnSelf,
    NoSuchDependency,
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

    pub fn depend(&mut self, dependent: T, dependency: T) -> Result<(), ErrSoydeps> {
        if dependent == dependency {
            return Err(ErrSoydeps::DependsOnSelf);
        }

        if self.depends_on(&dependency, &dependent) {
            return Err(ErrSoydeps::CircularDependency);
        }

        self.nodes.insert(dependent.clone());
        self.nodes.insert(dependency.clone());

        let dependencies = self
            .dependents
            .entry(dependency.clone())
            .or_insert(HashSet::from([dependent.clone()]));

        let dependents = self
            .dependencies
            .entry(dependent.clone())
            .or_insert(HashSet::from([dependency.clone()]));

        // Check before insert, to avoid redundant clones
        if !dependencies.contains(&dependency) {
            dependencies.insert(dependency.clone());
        }

        if !dependents.contains(&dependent) {
            dependencies.insert(dependent.clone());
        }

        Ok(())
    }

    pub fn dependencies(&self, node: &T) -> HashSet<T> {
        let mut search_next = vec![node];
        let mut result = HashSet::<T>::new();

        while !search_next.is_empty() {
            let mut discovered = Vec::new();

            for next in search_next.iter() {
                let dependencies = self.dependencies.get(next);
                if dependencies.is_none() {
                    continue;
                }

                for dep in dependencies.unwrap() {
                    if result.contains(dep) {
                        continue;
                    }

                    discovered.push(dep);
                    result.insert(dep.clone());
                }
            }

            search_next = discovered;
        }

        result
    }

    pub fn depends_on(&self, dependent: &T, dependency: &T) -> bool {
        self.dependencies(dependent).contains(dependency)
    }
}

impl std::fmt::Debug for ErrSoydeps {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircularDependency => write!(f, "circular dependency"),
            Self::DependenciesExists => write!(f, "dependencies exist"),
            Self::DependsOnSelf => write!(f, "depends on self"),
            Self::NoSuchDependency => write!(f, "no such dependency relationship"),
            Self::NoSuchNode => write!(f, "no such node"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Graph;

    #[test]
    fn test_basic_dependency() {
        let mut g = Graph::<&str>::default();
        g.depend("stardust", "bigbang")
            .expect("1st insert should succeed");

        g.depend("star", "stardust")
            .expect("2nd insert star->stardust should succeed");

        assert_eq!(true, g.depends_on(&"star", &"stardust"));
        assert_eq!(true, g.depends_on(&"star", &"bigbang"));
        assert_eq!(true, g.depends_on(&"stardust", &"bigbang"));
        assert_eq!(false, g.depends_on(&"bigbang", &"dust"));

        g.depend("proto-planet", "star").unwrap();
        g.depend("planet", "proto-planet").unwrap();

        assert_eq!(true, g.depends_on(&"planet", &"bigbang"));
        assert_eq!(true, g.depends_on(&"planet", &"stardust"));
        assert_eq!(true, g.depends_on(&"planet", &"star"));
        assert_eq!(true, g.depends_on(&"planet", &"proto-planet"));

        assert_eq!(true, g.depends_on(&"proto-planet", &"bigbang"));
        assert_eq!(true, g.depends_on(&"proto-planet", &"stardust"));
        assert_eq!(true, g.depends_on(&"proto-planet", &"star"));

        assert_eq!(true, g.depends_on(&"star", &"bigbang"));
        assert_eq!(true, g.depends_on(&"star", &"stardust"));

        assert_eq!(true, g.depends_on(&"stardust", &"bigbang"));

        assert_eq!(false, g.depends_on(&"bigbang", &"planet"));
        assert_eq!(false, g.depends_on(&"stardust", &"planet"));
        assert_eq!(false, g.depends_on(&"star", &"planet"));
        assert_eq!(false, g.depends_on(&"proto-planet", &"planet"));
        assert_eq!(false, g.depends_on(&"planet", &"planet"));

        assert_eq!(false, g.depends_on(&"bigbang", &"proto-planet"));
        assert_eq!(false, g.depends_on(&"stardust", &"proto-planet"));
        assert_eq!(false, g.depends_on(&"star", &"proto-planet"));
        assert_eq!(false, g.depends_on(&"proto-planet", &"proto-planet"));

        assert_eq!(false, g.depends_on(&"bigbang", &"star"));
        assert_eq!(false, g.depends_on(&"stardust", &"star"));
        assert_eq!(false, g.depends_on(&"star", &"star"));

        assert_eq!(false, g.depends_on(&"bigbang", &"stardust"));
        assert_eq!(false, g.depends_on(&"stardust", &"stardust"));

        g.depend("stardust", "star")
            .expect_err("stardust should not depend on star");
    }
}
