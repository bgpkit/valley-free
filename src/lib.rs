/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashMap, HashSet},
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
        if path.contains(&asn) {
            // detected a loop
            return;
        }

        // reaching here means the path + current as should be good to use
        let mut new_path = path.clone();
        new_path.push(asn);
        all_paths.push(new_path.clone());

        if seen.contains(&asn) {
            // we have seen this AS from other branches, meaning we have tried propagation from
            // this AS already. so we skip propagation here.
            // NOTE: we still add this path to the paths list. see `test_multiple_paths_to_origin`
            //       test function for more.
            return;
        }

        seen.insert(asn);

        let as_ptr = self.ases_map.get(&asn).unwrap();
        match dir {
            Direction::UP => {
                // we are propagating up in the current step, thus we can
                // continue to all directions
                for customer_asn in &as_ptr.customers {
                    self.propagate_paths(
                        all_paths,
                        *customer_asn,
                        Direction::DOWN,
                        new_path.clone(),
                        seen,
                    );
                }

                for peer_asn in &as_ptr.peers {
                    self.propagate_paths(
                        all_paths,
                        *peer_asn,
                        Direction::PEER,
                        new_path.clone(),
                        seen,
                    );
                }

                for provider_asn in &as_ptr.providers {
                    self.propagate_paths(
                        all_paths,
                        *provider_asn,
                        Direction::UP,
                        new_path.clone(),
                        seen,
                    );
                }
            }
            Direction::DOWN | Direction::PEER => {
                for customer_asn in &as_ptr.customers {
                    self.propagate_paths(
                        all_paths,
                        *customer_asn,
                        Direction::DOWN,
                        new_path.clone(),
                        seen,
                    );
                }
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

    #[test]
    fn propagate() {
        let mut topo = Topology::new();
        let file = match File::open("20161101.as-rel.txt.bz2") {
            Ok(f) => f,
            Err(_) => panic!("cannot open file"),
        };
        let reader = BufReader::new(BzDecoder::new(&file));
        let res = topo.build_topology(reader);
        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 55809);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 15169, Direction::UP, vec![], &mut seen);
        dbg!(all_paths.len());
    }

    #[test]
    fn test_multiple_paths_to_origin() {
        let mut topo = Topology::new();
        let test_rel = r#"# xxx
1|2|-1
1|3|-1
2|4|-1
3|4|-1"#;
        let reader = BufReader::new(test_rel.as_bytes());
        let res = topo.build_topology(reader);
        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 4);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 1, Direction::UP, vec![], &mut seen);

        assert_eq!(all_paths.len(), 5);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1,2]));
        assert!(all_paths.contains(&vec![1,2,4]));
        assert!(all_paths.contains(&vec![1,3]));
        assert!(all_paths.contains(&vec![1,3,4]));
    }
}
