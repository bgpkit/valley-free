use bzip2::read::BzDecoder;
use std::fs::File;
use valley_free::*;

fn main() {
    let asn = 19604;
    let file = File::open("20231201.as-rel.txt.bz2").unwrap();
    let file = BzDecoder::new(&file);
    let topo = Topology::from_caida(file).unwrap();

    let (all_paths, seen) = topo.propagate_paths(asn, Direction::Up);
    dbg!(all_paths.len());
    dbg!(seen.len());
}
