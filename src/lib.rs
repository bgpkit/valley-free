/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashMap, HashSet},
    io::BufRead,
};

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
type Path = Vec<u32>;

/// Definiton of AS struct
#[derive(Clone)]
pub struct As {
    /// Autonomous system number
    pub asn: u32,

    /// Set of customer ASes
    pub customers: HashSet<u32>,

    /// Set of provider ASes
    pub providers: HashSet<u32>,

    /// Set of peer ASes
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
pub struct Topology {
    /// Hashmap of ASes: ASN (u32) to [As]
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

        if seen.contains(&asn) {
            // in current dps search, we've already gone through this AS from other paths
            // for example:
            // 1,2 -> 1,2,3 -> 1,4
            // 1,4,2 will be triggered here
            // NOTE: this might produce some false negative
            return;
        }

        // reaching here means the path + current as should be good to use
        let mut new_path = path.clone();
        new_path.push(asn);
        all_paths.push(new_path.clone());
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
}
