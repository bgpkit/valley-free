/// valley-free-rs is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.

use std::{collections::{HashMap, HashSet}, fs::File, io::{BufReader, BufRead}};
use bzip2::read::BzDecoder;

pub enum RelType {
    CUSTOMER,
    PROVIDER,
    PEER,
}

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
}

#[cfg(test)]
mod tests {
    use crate::Topology;

    #[test]
    fn build_topology() {
        let mut topo = Topology::new("20161101.as-rel.txt.bz2");
        let res = topo.build_topology();

        assert!(res.is_ok());
        assert_eq!(topo.ases_map.len(), 55809);
    }
}
