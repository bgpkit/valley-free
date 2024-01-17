use petgraph::graph::NodeIndex;
use valley_free::{RelType, Topology};

type GraphPath = Vec<NodeIndex>;

fn main() {
    let topo = Topology::from_edges(vec![
        (1, 2, RelType::ProviderToCustomer),
        (1, 3, RelType::ProviderToCustomer),
        (2, 3, RelType::PearToPear),
        (2, 4, RelType::ProviderToCustomer),
        (3, 4, RelType::ProviderToCustomer),
    ]);

    let start = 4;
    let topo = topo.paths_graph(start);

    let start_idx = topo.index_of(start).unwrap(); // Node index
    let mut stack: Vec<(NodeIndex, GraphPath)> = vec![(start_idx, vec![start_idx])];
    let mut visited: Vec<NodeIndex> = vec![];
    let mut all_paths: Vec<GraphPath> = vec![];

    while !stack.is_empty() {
        let (node_idx, path) = stack.pop().unwrap();

        if visited.contains(&node_idx) {
            continue;
        }

        visited.push(node_idx);
        all_paths.push(path.clone());

        let childrens = topo
            .raw_graph()
            .neighbors_directed(node_idx, petgraph::Direction::Outgoing)
            .map(|child_idx| {
                let mut path = path.clone();
                path.push(child_idx);
                (child_idx, path)
            });
        stack.extend(childrens);
    }

    for path in all_paths {
        let path = path
            .iter()
            .map(|node_idx| topo.asn_of(*node_idx))
            .collect::<Vec<_>>();

        println!("{:?}", path);
    }
}
