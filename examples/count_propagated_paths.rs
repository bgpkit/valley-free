use std::{fs::File, io::BufReader, collections::HashSet};
use valley_free::*;
use bzip2::read::BzDecoder;

fn main(){
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
