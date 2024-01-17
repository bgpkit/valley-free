use std::fs::File;

use petgraph::algo::all_simple_paths;
use valley_free::Topology;

fn main() {
    let file = File::open("20231201.as-rel.txt").unwrap();
    let topo = Topology::from_caida(file).unwrap();

    let university_of_twente_asn = 1133;
    let universidade_de_sao_paulo_asn = 28571;
    let ut_path = topo.paths_graph(university_of_twente_asn);

    let paths = all_simple_paths::<Vec<_>, _>(
        &ut_path.graph,
        ut_path.index_of(university_of_twente_asn).unwrap(),
        ut_path.index_of(universidade_de_sao_paulo_asn).unwrap(),
        0,
        None,
    );

    println!("Paths from UT to USP:");
    for path in paths {
        let path = path
            .iter()
            .map(|node| ut_path.asn_of(*node))
            .collect::<Vec<_>>();
        println!("  {:?}", path);
    }
}
