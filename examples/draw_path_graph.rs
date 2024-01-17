use petgraph::dot::Dot;
use valley_free::{RelType, Topology};

fn main() {
    let topo = Topology::from_edges(vec![
        (1, 2, RelType::ProviderToCustomer),
        (1, 3, RelType::ProviderToCustomer),
        (2, 4, RelType::ProviderToCustomer),
        (2, 5, RelType::ProviderToCustomer),
        (2, 3, RelType::PearToPear),
        (3, 5, RelType::ProviderToCustomer),
        (3, 6, RelType::ProviderToCustomer),
    ]);

    println!("Basic topology");
    println!("{:?}", Dot::new(&topo.graph));

    let topo_path = topo.paths_graph(4);
    println!("Path topology");
    println!("{:?}", Dot::new(&topo_path.graph));

    // You can visualize the graphs online at https://dreampuf.github.io/GraphvizOnline/
}
