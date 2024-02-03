use valley_free::{RelType, Topology};

fn main() {
    let topo = Topology::from_edges(vec![
        (1, 2, RelType::ProviderToCustomer),
        (1, 3, RelType::ProviderToCustomer),
        (2, 3, RelType::PearToPear),
        (2, 4, RelType::ProviderToCustomer),
        (3, 4, RelType::ProviderToCustomer),
    ]);

    let topo = topo.valley_free_of(4);

    for path in topo.path_to_all_ases().unwrap() {
        println!("{:?}", path);
    }
}
