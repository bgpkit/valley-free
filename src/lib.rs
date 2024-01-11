/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashMap, HashSet, VecDeque},
    io::BufRead,
};
use std::{fs::File, io::BufReader};

use bzip2::read::BzDecoder;
use pyo3::prelude::*;
use pyo3::{exceptions::PyIOError, wrap_pyfunction};

/// AS relationship types: CUSTOMER, PROVIDER, and PEER
pub enum RelType {
    CUSTOMER,
    PROVIDER,
    PEER,
}

/// Direction of where the current current propagation going.
#[derive(PartialEq, Eq)]
pub enum Direction {
    /// Propagating to a provider AS
    UP,
    /// Propagating to a customer AS
    DOWN,
    /// Propagating to a peer AS
    PEER,
}

/// Define type alias Path as Vec<u32>
pub type Path = Vec<u32>;

/// Definiton of AS struct
#[pyclass]
#[derive(Clone)]
pub struct As {
    /// Autonomous system number
    #[pyo3(get, set)]
    pub asn: u32,

    /// Set of customer ASes
    #[pyo3(get, set)]
    pub customers: HashSet<u32>,

    /// Set of provider ASes
    #[pyo3(get, set)]
    pub providers: HashSet<u32>,

    /// Set of peer ASes
    #[pyo3(get, set)]
    pub peers: HashSet<u32>,
}

impl As {
    /// Insert another AS as related AS
    fn insert_rel(&mut self, rel_type: RelType, other: u32) {
        match rel_type {
            RelType::CUSTOMER => {
                self.customers.insert(other);
            }
            RelType::PEER => {
                self.peers.insert(other);
            }
            RelType::PROVIDER => {
                self.providers.insert(other);
            }
        }
    }
}

/// Definition of Topology
#[pyclass]
#[derive(FromPyObject)]
pub struct Topology {
    /// Hashmap of ASes: ASN (u32) to [As]
    #[pyo3(get)]
    pub ases_map: HashMap<u32, As>,
}

impl Topology {
    /// Constructor of the Topology struct
    pub fn new() -> Topology {
        Topology {
            ases_map: HashMap::new(),
        }
    }

    fn get_or_insert(&mut self, asn: u32) -> u32 {
        match self.ases_map.entry(asn) {
            std::collections::hash_map::Entry::Occupied(o) => o.into_mut(),
            std::collections::hash_map::Entry::Vacant(v) => v.insert(As {
                asn: asn,
                customers: HashSet::new(),
                providers: HashSet::new(),
                peers: HashSet::new(),
            }),
        }
        .asn
    }

    fn add_rel(&mut self, asn1: u32, asn2: u32, rel_type: RelType) {
        let as1 = self.ases_map.get_mut(&asn1).unwrap();
        as1.insert_rel(rel_type, asn2);
    }

    /// Build the Topology using [CAIDA AS-relationship][asrel] datafile.
    ///
    /// This function takes an reader that implements [BufRead] trait, read
    /// lines from the reader, and parse the input.
    ///
    /// The CAIDA's AS-relationship data is formatted as follows:
    /// ```example
    /// ## A FEW LINES OF COMMENT
    /// ## A FEW LINES OF COMMENT
    /// ## A FEW LINES OF COMMENT
    /// 1|7470|0
    /// 1|9931|-1
    /// 1|11537|0
    /// 1|25418|0
    /// 2|35000|0
    /// 2|263686|0
    /// ...
    /// ```
    ///
    /// The data format is:
    /// ```example
    /// <provider-as>|<customer-as>|-1
    /// <peer-as>|<peer-as>|0
    /// ```
    ///
    /// [asrel]: https://www.caida.org/data/as-relationships/
    pub fn build_topology(&mut self, reader: impl BufRead) -> Result<(), String> {
        for line in reader.lines() {
            let line: String = match line {
                Ok(l) => l,
                Err(e) => return Err(e.to_string()),
            };
            if line.starts_with("#") {
                continue;
            }
            let fields = line.split("|").collect::<Vec<&str>>();
            let asn1 = fields[0].parse::<u32>().unwrap();
            let asn2 = fields[1].parse::<u32>().unwrap();
            let rel = fields[2].parse::<i32>().unwrap();

            let asn1 = self.get_or_insert(asn1);
            let asn2 = self.get_or_insert(asn2);

            match rel {
                0 => {
                    // asn1 and asn2 are peers
                    self.add_rel(asn1, asn2, RelType::PEER);
                    self.add_rel(asn2, asn1, RelType::PEER);
                }
                -1 => {
                    // asn1 is the provider of asn2
                    self.add_rel(asn1, asn2, RelType::CUSTOMER);
                    self.add_rel(asn2, asn1, RelType::PROVIDER);
                }
                _ => return Err(format!("unknown relationship type {} in {}", rel, line)),
            }
        }

        Ok(())
    }

    /// Recursively calculate path propagation results.
    ///
    /// Recursion breaking conditions:
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
    /// let mut topo = Topology::new();
    /// let file = match File::open("20161101.as-rel.txt.bz2") {
    ///     Ok(f) => f,
    ///     Err(_) => panic!("cannot open file"),
    /// };
    /// let reader = BufReader::new(BzDecoder::new(&file));
    /// let res = topo.build_topology(reader);
    ///
    /// let mut all_paths = vec![];
    /// let mut seen = HashSet::new();
    /// topo.propagate_paths(&mut all_paths, 15169, Direction::UP, vec![], &mut seen);
    /// dbg!(all_paths.len());
    /// ```
    ///
    /// Arguments:
    /// - `all_paths`: a muttable Vector of [Path]s passed in to store explored paths
    /// - `asn`: the current ASN that will propagate paths
    /// - `dir`: the [Direction] of the propagation
    /// - `path`: the path so far(not including the current AS)
    /// - `seen`: a [HashSet] of ASes that it has explored already
    pub fn propagate_paths(
        &self,
        all_paths: &mut Vec<Path>,
        asn: u32,
        dir: Direction,
        path: Path,
        seen: &mut HashSet<u32>,
    ) {
        let mut up_path_queue = VecDeque::<Path>::new();
        let mut peer_path_queue = VecDeque::<Path>::new();
        let mut down_path_queue = VecDeque::<Path>::new();

        let path_join = |x: &Path, y: u32| -> Path {
            let mut new_path = x.clone();
            new_path.push(y);
            new_path
        };

        // Initialize the path queues depending on the first propagation direction
        let new_path = path_join(&path, asn);
        match dir {
            Direction::UP => up_path_queue.push_back(new_path.clone()),
            Direction::PEER => peer_path_queue.push_back(new_path.clone()),
            Direction::DOWN => down_path_queue.push_back(new_path.clone()),
        }
        all_paths.push(new_path);

        while !up_path_queue.is_empty() {
            let path = up_path_queue.pop_front().unwrap(); // While check if has elements
            let asn = path.last().unwrap(); // Always has at least one element

            // we have seen this AS from other branches, meaning we have tried propagation from
            // this AS already. so we skip propagation here.
            // NOTE: we still add this path to the paths list. see `test_multiple_paths_to_origin`
            //       test function for more.
            if seen.contains(asn) {
                continue;
            }
            seen.insert(*asn);

            let as_ptr = self.ases_map.get(asn).unwrap();

            for provider_asn in &as_ptr.providers {
                if path.contains(provider_asn) {
                    continue;
                }

                let new_path = path_join(&path, *provider_asn);
                all_paths.push(new_path.clone());
                up_path_queue.push_back(new_path);
            }

            for pear_asn in &as_ptr.peers {
                if path.contains(pear_asn) {
                    continue;
                }

                let new_path = path_join(&path, *pear_asn);
                all_paths.push(new_path.clone());
                peer_path_queue.push_back(new_path);
            }

            for customer_asn in &as_ptr.customers {
                // detected a loop
                if path.contains(customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, *customer_asn);
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

            let as_ptr = self.ases_map.get(asn).unwrap();

            for customer_asn in &as_ptr.customers {
                // detected a loop
                if path.contains(customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, *customer_asn);
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

            let as_ptr = self.ases_map.get(asn).unwrap();

            for customer_asn in &as_ptr.customers {
                // detected a loop
                if path.contains(customer_asn) {
                    continue;
                }

                let new_path = path_join(&path, *customer_asn);
                all_paths.push(new_path.clone());
                down_path_queue.push_back(new_path);
            }
        }
    }
}

/// Formats the sum of two numbers as string.
#[pyfunction]
fn load_topology<'a>(py: Python, file_path: String) -> PyResult<&PyCell<Topology>> {
    let mut topo = Topology::new();
    let file = match File::open(&file_path) {
        Ok(f) => f,
        Err(_) => panic!("cannot open file"),
    };
    let reader = BufReader::new(BzDecoder::new(&file));
    match topo.build_topology(reader) {
        Ok(_) => {
            let topo_cell = PyCell::new(py, topo).unwrap();
            Ok(topo_cell)
        }
        Err(_) => Err(PyIOError::new_err("cannot load topology file")),
    }
}

#[pyfunction]
fn propagate_paths<'a>(topo: &Topology, asn: u32) -> PyResult<Vec<Vec<u32>>> {
    let mut all_paths = vec![];
    let mut seen = HashSet::new();
    topo.propagate_paths(&mut all_paths, asn, Direction::UP, vec![], &mut seen);
    Ok(all_paths)
}

/// A Python module implemented in Rust.
#[pymodule]
fn valley_free(_: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(load_topology, m)?)?;
    m.add_function(wrap_pyfunction!(propagate_paths, m)?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{fs::File, io::BufReader};

    use crate::*;
    use bzip2::read::BzDecoder;

    #[test]
    fn build_topology() {
        let mut topo = Topology::new();
        let file = match File::open("20161101.as-rel.txt.bz2") {
            Ok(f) => f,
            Err(_) => panic!("cannot open file"),
        };
        let reader = BufReader::new(BzDecoder::new(&file));
        let res = topo.build_topology(reader);

        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 55809);
    }

    fn topology_from_str(test_rel: &str) -> Topology {
        let mut topo = Topology::new();
        let reader = BufReader::new(test_rel.as_bytes());
        let res = topo.build_topology(reader);
        assert!(res.is_ok());
        topo
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
        let topo = topology_from_str("1|2|-1\n2|3|-1");

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::DOWN, vec![], &mut seen);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::PEER, vec![], &mut seen);
        assert_eq!(all_paths.len(), 3);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::UP, vec![], &mut seen);
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
        let topo = topology_from_str("1|2|0\n2|3|-1");

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::UP, vec![], &mut seen);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::PEER, vec![], &mut seen);
        assert_eq!(all_paths.len(), 1);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::DOWN, vec![], &mut seen);
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
        let topo = topology_from_str("2|1|-1\n2|3|0\n3|4|-1");

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::UP, vec![], &mut seen);

        assert_eq!(all_paths.len(), 4);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));
        assert!(all_paths.contains(&vec![1, 2, 3, 4]));

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::PEER, vec![], &mut seen);
        assert_eq!(all_paths.len(), 1);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::DOWN, vec![], &mut seen);
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
        let test_rel = r#"# xxx
1|2|-1
1|3|-1
2|4|-1
3|4|-1"#;
        let topo = topology_from_str(test_rel);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::UP, vec![], &mut seen);

        dbg!(&all_paths);
        assert_eq!(all_paths.len(), 5);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 4]));
        assert!(all_paths.contains(&vec![1, 3]));
        assert!(all_paths.contains(&vec![1, 3, 4]));
    }

    // Issue #4
    #[test]
    fn test_works_in_any_provider_order() {
        let test_rel = r#"# xxx
3356|6453|0
3356|3|0
3356|4|-1
6453|4|-1"#;

        let get_providers = |topo: &Topology| -> Vec<u32> {
            topo.ases_map
                .get(&4)
                .unwrap()
                .providers
                .clone()
                .into_iter()
                .collect()
        };

        let mut topo1 = Topology::new();

        let reader = BufReader::new(test_rel.as_bytes());
        topo1.build_topology(reader).unwrap();

        let providers1 = get_providers(&topo1);

        let topo2 = loop {
            let mut topo2 = Topology::new();
            let reader = BufReader::new(test_rel.as_bytes());
            topo2.build_topology(reader).unwrap();

            let providers2 = get_providers(&topo2);

            if providers1 != providers2 {
                break topo2;
            }
        };

        let mut all_paths1 = vec![];
        let mut seen1 = HashSet::new();
        topo1.propagate_paths(&mut all_paths1, 4, Direction::UP, vec![], &mut seen1);

        let mut all_paths2 = vec![];
        let mut seen2 = HashSet::new();
        topo2.propagate_paths(&mut all_paths2, 4, Direction::UP, vec![], &mut seen2);

        assert_eq!(all_paths1.len(), all_paths2.len());
        assert_eq!(seen1, seen2);
        assert!(seen1.contains(&3));
        assert!(seen2.contains(&3));
    }
}
