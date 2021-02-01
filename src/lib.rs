/// valley-free-rs is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.

use std::{collections::{HashMap, HashSet}, fs::File, io::{BufReader, BufRead}};
use bzip2::read::BzDecoder;

/// AS relationship types
pub enum RelType {
    CUSTOMER,
    PROVIDER,
    PEER,
}

/// Direction of where the current current propagation going.
pub enum Direction {
    UP,
    DOWN,
    PEER
}

type Path = Vec<u32>;


/// definiton of AS struct
pub struct As {
    /// Autonomous system number
    pub asn: u32,

    /// HashMap of customer ASes
    pub customers: HashSet<u32>,

    /// HashMap of provider ASes
    pub providers: HashSet<u32>,

    /// HashMap of peer ASes
    pub peers: HashSet<u32>,
}

impl As {
    pub fn insert_rel(&mut self, rel_type: RelType, other: u32) {
        match rel_type{
            RelType::CUSTOMER => {
                self.customers.insert(other);
            },
            RelType::PEER => {
                self.peers.insert(other);
            },
            RelType::PROVIDER => {
                self.providers.insert(other);
            },
        }
    }
}

/// definition of Topology
pub struct Topology {
    /// hashmap of ASes
    pub ases_map: HashMap<u32, As>,
    /// topology data file
    pub topo_file: String,
}

impl Topology {

    pub fn new(rel_file_path: &str) -> Topology {
        Topology{
            ases_map: HashMap::new(),
            topo_file: rel_file_path.to_owned()
        }
    }

    fn get_or_insert(&mut self, asn: u32) -> u32{
        match self.ases_map.entry(asn) {
            std::collections::hash_map::Entry::Occupied(o) => {o.into_mut()}
            std::collections::hash_map::Entry::Vacant(v) => {v.insert(
                As{asn: asn, customers: HashSet::new(), providers: HashSet::new(), peers: HashSet::new()}
            )}
        }.asn
    }

    fn add_rel(&mut self, asn1: u32, asn2: u32, rel_type: RelType) {
        let as1 = self.ases_map.get_mut(&asn1).unwrap();
        as1.insert_rel(rel_type, asn2);
    }

    pub fn build_topology(&mut self) -> Result<(), String>{

        let file = match File::open(&self.topo_file) {
            Ok(f) => f,
            Err(_) => return Err(format!("cannot open file {}", self.topo_file))
        };

        let reader = BufReader::new(BzDecoder::new(&file));
        for line in reader.lines(){
            let line: String = line.unwrap();
            if line.starts_with("#") {
                continue
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
                },
                -1 => {
                    // asn1 is the provider of asn2
                    self.add_rel(asn1, asn2, RelType::CUSTOMER);
                    self.add_rel(asn2, asn1, RelType::PROVIDER);
                }
                _ => {
                    return Err(format!("unknown relationship type {} in {}", rel, line))
                }
            }
        }

        Ok(())
    }

    pub fn propagate_paths(&self, all_paths: &mut Vec<Path>, asn: u32, dir: Direction, path: Path, seen: &mut HashSet<u32>) {
        if path.contains(&asn) {
            // detected a loop
            return
        }

        if seen.contains(&asn) {
            // in current dps search, we've already gone through this AS from other paths
            // for example:
            // 1,2 -> 1,2,3 -> 1,4
            // 1,4,2 will be triggered here
            // NOTE: this might produce some false negative
            return
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
                    self.propagate_paths(all_paths, *customer_asn, Direction::DOWN, new_path.clone(), seen);
                }

                for peer_asn in &as_ptr.peers {
                    self.propagate_paths(all_paths, *peer_asn, Direction::PEER, new_path.clone(), seen);
                }

                for provider_asn in &as_ptr.providers {
                    self.propagate_paths(all_paths, *provider_asn, Direction::UP, new_path.clone(), seen);
                }
            },
            Direction::DOWN|Direction::PEER => {
                for customer_asn in &as_ptr.customers {
                    self.propagate_paths(all_paths, *customer_asn, Direction::DOWN, new_path.clone(), seen);
                }
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn build_topology() {
        let mut topo = Topology::new("20161101.as-rel.txt.bz2");
        let res = topo.build_topology();

        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 55809);
    }

    #[test]
    fn propagate() {
        let mut topo = Topology::new("20161101.as-rel.txt.bz2");
        let res = topo.build_topology();
        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 55809);

        let mut all_paths = vec![];
        let mut seen = HashSet::new();
        topo.propagate_paths(&mut all_paths, 15169, Direction::UP, vec![], &mut seen);
        dbg!(all_paths.len());
    }
}
