use std::fs::File;

use valley_free::Topology;

fn main() {
    let file = File::open("20231201.as-rel.txt").unwrap();
    let topo = Topology::from_caida(file).unwrap();

    let university_of_twente_asn = 1133;
    let universidade_de_sao_paulo_asn = 28571;
    let ut_path = topo.paths_graph(university_of_twente_asn);

    // Use A* to find the shortest path between two nodes
    let path = ut_path
        .shortest_path_to(university_of_twente_asn, universidade_de_sao_paulo_asn)
        .unwrap();

    println!("Path from UT to USP: {:?}", path);
}
