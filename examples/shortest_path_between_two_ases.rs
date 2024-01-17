use std::fs::File;

use petgraph::algo::astar;
use valley_free::{RelType, Topology};

fn main() {
    let file = File::open("20231201.as-rel.txt").unwrap();
    let topo = Topology::from_caida(file).unwrap();

    let university_of_twente_asn = 1133;
    let universidade_de_sao_paulo_asn = 28571;
    let ut_path = topo.paths_graph(university_of_twente_asn);

    // Use A* to find the shortest path between two nodes
    let (_len, path) = astar(
        ut_path.graph,
        ut_path.index_of(university_of_twente_asn).unwrap(),
        |finish| finish == ut_path.index_of(universidade_de_sao_paulo_asn).unwrap(),
        |edge| match edge.weight() {
            // priorize pearing
            RelType::PearToPear => 0,
            RelType::ProviderToCustomer => 1,
            RelType::CustomerToProvider => 2,
        },
        |_| 0,
    )
    .unwrap();
    let path = path
        .iter()
        .map(|node| ut_path.asn_of(*node))
        .collect::<Vec<_>>();

    println!("Path from UT to USP: {:?}", path);
}
