/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashSet, VecDeque},
    convert::TryInto,
    io,
};

use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum RelType {
    ProviderToCustomer,
    PearToPear,
}

// Required to work as a edge
impl Default for RelType {
    fn default() -> Self {
        RelType::ProviderToCustomer
    }
}

pub enum Direction {
    Up,
    Peer,
    Down,
}

pub type TopologyPath = Vec<u32>;
type TopologyPathIndex = Vec<NodeIndex>;

pub struct Topology(DiGraph<u32, RelType>);

#[derive(Debug)]
pub enum TopologyError {
    IoError(io::Error),
    ParseAsnError(std::num::ParseIntError),
    ParseError(String),
}

impl Topology {
    pub fn from_edges(edges: Vec<(u32, u32, RelType)>) -> Self {
        let edges: HashSet<_> = edges
            .into_iter()
            .flat_map(|(asn1, asn2, rel)| match rel {
                RelType::ProviderToCustomer => {
                    vec![(asn1, asn2, RelType::ProviderToCustomer)]
                }
                RelType::PearToPear => vec![
                    (asn1, asn2, RelType::PearToPear),
                    (asn2, asn1, RelType::PearToPear),
                ],
            })
            .collect();

        Topology(DiGraph::from_edges(edges))
    }

    pub fn from_caida(reader: impl std::io::Read) -> Result<Self, TopologyError> {
        let content = reader
            .bytes()
            .collect::<Result<Vec<u8>, _>>()
            .map_err(TopologyError::IoError)?;

        let content = String::from_utf8(content).map_err(|e| {
            TopologyError::ParseError(format!("invalid UTF-8 in AS relationship file: {}", e))
        })?;

        let edges = content
            .lines()
            .filter(|line| !line.starts_with("#"))
            .map(|line| {
                let fields = line.split("|").collect::<Vec<&str>>();
                let asn1 = fields[0]
                    .parse::<u32>()
                    .map_err(TopologyError::ParseAsnError)?;
                let asn2 = fields[1]
                    .parse::<u32>()
                    .map_err(TopologyError::ParseAsnError)?;
                let rel = fields[2]
                    .parse::<i32>()
                    .map_err(TopologyError::ParseAsnError)?;

                match rel {
                    // asn1 and asn2 are peers
                    0 => Ok((asn1, asn2, RelType::PearToPear)),

                    // asn1 is a provider of asn2
                    -1 => Ok((asn1, asn2, RelType::ProviderToCustomer)),

                    _ => Err(TopologyError::ParseError(format!(
                        "unknown relationship type {} in {}",
                        rel, line
                    ))),
                }
            })
            .collect::<Result<Vec<(u32, u32, RelType)>, _>>()?;

        Ok(Topology::from_edges(edges))
    }

    pub fn providers_of(&self, asn: NodeIndex) -> HashSet<NodeIndex> {
        self.0
            .edges_directed(asn, petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| edge.source())
            .collect()
    }

    pub fn customers_of(&self, asn: NodeIndex) -> HashSet<NodeIndex> {
        self.0
            .edges_directed(asn, petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| edge.target())
            .collect()
    }

    pub fn peers_of(&self, asn: NodeIndex) -> HashSet<NodeIndex> {
        self.0
            .edges_directed(asn, petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::PearToPear)
            .map(|edge| edge.target())
            .collect()
    }

    pub fn asn_of(&self, asn: NodeIndex) -> u32 {
        asn.index().try_into().unwrap()
    }

    /// Calculate path propagation results transversing the topology from a given AS.
    /// Uses BFS to traverse the topology, propagating first to providers, then to peers,
    /// and finally to customers.
    ///
    /// Breaking conditions:
    /// 1. loop detected;
    /// 2. previously propagated from the AS;
    /// 3. all connected ASes have been called
    ///
    /// Propagation logic:
    /// 1. if the current path is propagated from a customer, then it can
    /// propagate to all of its' customers, providers, and peers
    /// 2. if the current path is propagated from a provider or a peer, it can
    /// only propagate to its customers (thus achiving valley-free)
    ///
    /// Full example: to explore all paths toward AS123, call
    /// ```no_run
    /// use std::{fs::File, io::BufReader, collections::HashSet};
    /// use valley_free::*;
    /// use bzip2::read::BzDecoder;
    ///
    /// let file = File::open("20161101.as-rel.txt.bz2").unwrap();
    /// let topo = Topology::from_caida(BzDecoder::new(&file)).unwrap();
    ///
    /// let (all_paths, seen) = topo.propagate_paths(15169, Direction::Up);
    /// dbg!(all_paths.len());
    /// ```
    ///
    /// Arguments:
    /// - `from_asn`: the current ASN that will propagate paths
    /// - `dir`: the [Direction] of the propagation
    pub fn propagate_paths(
        &self,
        from_asn: u32,
        dir: Direction,
    ) -> (Vec<TopologyPath>, HashSet<u32>) {
        let path: TopologyPathIndex = vec![];
        let mut all_paths: Vec<TopologyPathIndex> = vec![];
        let mut seen = HashSet::new();

        let mut up_path_queue = VecDeque::<TopologyPathIndex>::new();
        let mut peer_path_queue = VecDeque::<TopologyPathIndex>::new();
        let mut down_path_queue = VecDeque::<TopologyPathIndex>::new();

        let path_join = |x: &Vec<NodeIndex>, y: NodeIndex| -> TopologyPathIndex {
            let mut new_path = x.clone();
            new_path.push(y.into());
            new_path
        };

        // Initialize the path queues depending on the first propagation direction
        let new_path = path_join(&path, from_asn.into());
        match dir {
            Direction::Up => up_path_queue.push_back(new_path.clone()),
            Direction::Peer => peer_path_queue.push_back(new_path.clone()),
            Direction::Down => down_path_queue.push_back(new_path.clone()),
        }
        all_paths.push(new_path);

        while !up_path_queue.is_empty() {
            let path = up_path_queue.pop_front().unwrap(); // While check if has elements
            let asn = *path.last().unwrap(); // Always has at least one element

            // we have seen this AS from other branches, meaning we have tried propagation from
            // this AS already. so we skip propagation here.
            // NOTE: we still add this path to the paths list. see `test_multiple_paths_to_origin`
            //       test function for more.
            if seen.contains(&asn) {
                continue;
            }
            seen.insert(asn);

            for provider_asn in self.providers_of(asn.into()) {
                if path.contains(&provider_asn) {
                    continue;
                }

                let new_path = path_join(&path, provider_asn);
                all_paths.push(new_path.clone());
                up_path_queue.push_back(new_path);
            }

            for pear_asn in self.peers_of(asn.into()) {
                if path.contains(&pear_asn) {
                    continue;
                }

                let new_path = path_join(&path, pear_asn);
                all_paths.push(new_path.clone());
                peer_path_queue.push_back(new_path);
            }

            for customer_asn in self.customers_of(asn) {
                // detected a loop
                if path.contains(&customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, customer_asn);
                all_paths.push(new_path.clone());
                down_path_queue.push_back(new_path);
            }
        }

        while !peer_path_queue.is_empty() {
            let path = peer_path_queue.pop_front().unwrap();
            let asn = path.last().unwrap();

            if seen.contains(asn) {
                continue;
            }
            seen.insert(*asn);

            for customer_asn in self.customers_of(*asn) {
                // detected a loop
                if path.contains(&customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, customer_asn);
                all_paths.push(new_path.clone());
                down_path_queue.push_back(new_path);
            }
        }

        while !down_path_queue.is_empty() {
            let path = down_path_queue.pop_front().unwrap();
            let asn = path.last().unwrap();

            if seen.contains(asn) {
                continue;
            }
            seen.insert(*asn);

            for customer_asn in self.customers_of(*asn) {
                // detected a loop
                if path.contains(&customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, customer_asn);
                all_paths.push(new_path.clone());
                down_path_queue.push_back(new_path);
            }
        }

        let all_paths: Vec<TopologyPath> = all_paths
            .into_iter()
            .map(|path| path.into_iter().map(|x| self.asn_of(x)).collect())
            .collect();

        let seen: HashSet<u32> = seen.into_iter().map(|x| self.asn_of(x)).collect();

        (all_paths, seen)
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;

    use bzip2::read::BzDecoder;

    use super::*;

    /*
     *       ┌───────┐
     *       │   1   │
     *       └───┬───┘
     *     ┌─────┴─────┐
     * ┌───▼───┐   ┌───▼───┐
     * │   2   │   │   3   │
     * └───┬───┘   └───┬───┘
     *     └─────┬─────┘
     *       ┌───▼───┐
     *       │   4   │
     *       └───────┘
     */
    fn diamond_topology() -> Topology {
        Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (1, 3, RelType::ProviderToCustomer),
            (3, 2, RelType::PearToPear),
            (3, 4, RelType::ProviderToCustomer),
            (2, 4, RelType::ProviderToCustomer),
        ])
    }

    #[test]
    fn test_providers() {
        let topo = diamond_topology();

        assert_eq!(topo.providers_of(1.into()), [].into());
        assert_eq!(topo.providers_of(2.into()), [1.into()].into());
        assert_eq!(topo.providers_of(3.into()), [1.into()].into());
        assert_eq!(topo.providers_of(4.into()), [2.into(), 3.into()].into());
    }

    #[test]
    fn test_customers() {
        let topo = diamond_topology();

        assert_eq!(topo.customers_of(1.into()), [3.into(), 2.into()].into());
        assert_eq!(topo.customers_of(2.into()), [4.into()].into());
        assert_eq!(topo.customers_of(3.into()), [4.into()].into());
        assert_eq!(topo.customers_of(4.into()), [].into());
    }

    #[test]
    fn test_peers() {
        let topo = diamond_topology();

        assert_eq!(topo.peers_of(1.into()), [].into());
        assert_eq!(topo.peers_of(2.into()), [3.into()].into());
        assert_eq!(topo.peers_of(3.into()), [2.into()].into());
        assert_eq!(topo.peers_of(4.into()), [].into());
    }

    #[test]
    fn test_asn_of() {
        let topo = Topology::from_edges(vec![(1, 2, RelType::ProviderToCustomer)]);

        assert_eq!(topo.asn_of(1.into()), 1);
        assert_eq!(topo.asn_of(2.into()), 2);
    }

    #[test]
    fn test_from_caida() {
        let test_rel = r#"# xxx
1|2|-1
1|3|-1
2|4|-1
3|4|-1"#;
        let topo = Topology::from_caida(test_rel.as_bytes());

        assert!(topo.is_ok());
    }

    #[test]
    fn test_from_real_caida_data() {
        let file = File::open("20161101.as-rel.txt.bz2").unwrap();
        let reader = BzDecoder::new(&file);
        let topo = Topology::from_caida(reader);

        assert!(topo.is_ok());
    }

    #[test]
    /*
     * ┌───────┐
     * │   1   │
     * └───┬───┘
     *     │
     *     ▼
     * ┌───────┐
     * │   2   │
     * └───┬───┘
     *     │
     *     ▼
     * ┌───────┐
     * │   3   │
     * └───────┘
     */
    fn propagate_down_topology() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (2, 3, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 3);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);
        assert_eq!(all_paths.len(), 3);
    }

    #[test]
    /*
     * ┌───────┐    ┌───────┐
     * │   1   │◄──►│   2   │
     * └───────┘    └───┬───┘
     *                  │
     *                  ▼
     *              ┌───────┐
     *              │   3   │
     *              └───────┘
     */
    fn propagate_peer_topology() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::PearToPear),
            (2, 3, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 1);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);
        assert_eq!(all_paths.len(), 1);
    }

    #[test]
    /*
     * ┌───────┐    ┌───────┐
     * │   2   │◄──►│   3   │
     * └───┬───┘    └───┬───┘
     *     │            │
     *     ▼            ▼
     * ┌───────┐    ┌───────┐
     * │   1   │    │   4   │
     * └───────┘    └───────┘
     */
    fn propagate_up_topology() {
        let topo = Topology::from_edges(vec![
            (2, 1, RelType::ProviderToCustomer),
            (2, 3, RelType::PearToPear),
            (3, 4, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        assert_eq!(all_paths.len(), 4);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));
        assert!(all_paths.contains(&vec![1, 2, 3, 4]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 1);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);
        assert_eq!(all_paths.len(), 1);
    }

    #[test]
    /*
     *       ┌───────┐
     *       │   1   │
     *       └───┬───┘
     *           │
     *     ┌─────┴─────┐
     *     │           │
     * ┌───▼───┐   ┌───▼───┐
     * │   2   │   │   3   │
     * └───┬───┘   └───┬───┘
     *     │           │
     *     └─────┬─────┘
     *           │
     *       ┌───▼───┐
     *       │   4   │
     *       └───────┘
     */
    fn test_multiple_paths_to_origin() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (1, 3, RelType::ProviderToCustomer),
            (2, 4, RelType::ProviderToCustomer),
            (3, 4, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        dbg!(&all_paths);
        assert_eq!(all_paths.len(), 5);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 4]));
        assert!(all_paths.contains(&vec![1, 3]));
        assert!(all_paths.contains(&vec![1, 3, 4]));
    }

    /*
     * Issue #4 test case
     * ┌────────┐     ┌────────┐       ┌───────┐
     * │  3356  ├─────┤  6453  │◄─────►│   3   │
     * └───┬────┘     └────┬───┘       └───────┘
     *     │               │
     *     └───────┬───────┘
     *             │
     *         ┌───▼───┐
     *         │   4   │
     *         └───────┘
     */
    #[test]
    fn test_works_in_any_provider_order() {
        let edges = vec![
            (3356, 6453, RelType::PearToPear),
            (3356, 3, RelType::PearToPear),
            (3356, 4, RelType::ProviderToCustomer),
            (6453, 4, RelType::ProviderToCustomer),
        ];

        let topo1 = Topology::from_edges(edges.clone());

        for _ in 0..10 {
            let topo2 = Topology::from_edges(edges.clone());

            if topo1.providers_of(4.into()) != topo2.providers_of(4.into()) {
                let (all_paths1, seen1) = topo1.propagate_paths(4, Direction::Up);
                let (all_paths2, seen2) = topo2.propagate_paths(4, Direction::Up);

                assert_eq!(all_paths1.len(), all_paths2.len());
                assert_eq!(seen1, seen2);
                assert!(seen1.contains(&3));
                assert!(seen2.contains(&3));
            }
        }
    }
}
