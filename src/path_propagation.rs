#[cfg(test)]
mod tests {
    use super::*;
    use crate::topology::{RelType, Topology};

    #[test]
    /*
     * ┌───────┐
     * │   1   │
     * └───┬───┘
     *     │
     *     ▼
     * ┌───────┐
     * │   2   │
     * └───┬───┘
     *     │
     *     ▼
     * ┌───────┐
     * │   3   │
     * └───────┘
     */
    fn propagate_down_topology() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (2, 3, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 3);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);
        assert_eq!(all_paths.len(), 3);
    }

    #[test]
    /*
     * ┌───────┐    ┌───────┐
     * │   1   │◄──►│   2   │
     * └───────┘    └───┬───┘
     *                  │
     *                  ▼
     *              ┌───────┐
     *              │   3   │
     *              └───────┘
     */
    fn propagate_peer_topology() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::PearToPear),
            (2, 3, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        assert_eq!(all_paths.len(), 3);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 1);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);
        assert_eq!(all_paths.len(), 1);
    }

    #[test]
    /*
     * ┌───────┐    ┌───────┐
     * │   2   │◄──►│   3   │
     * └───┬───┘    └───┬───┘
     *     │            │
     *     ▼            ▼
     * ┌───────┐    ┌───────┐
     * │   1   │    │   4   │
     * └───────┘    └───────┘
     */
    fn propagate_up_topology() {
        let topo = Topology::from_edges(vec![
            (2, 1, RelType::ProviderToCustomer),
            (2, 3, RelType::PearToPear),
            (3, 4, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        assert_eq!(all_paths.len(), 4);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 3]));
        assert!(all_paths.contains(&vec![1, 2, 3, 4]));

        let (all_paths, _) = topo.propagate_paths(1, Direction::Peer);
        assert_eq!(all_paths.len(), 1);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Down);
        assert_eq!(all_paths.len(), 1);
    }

    #[test]
    /*
     *       ┌───────┐
     *       │   1   │
     *       └───┬───┘
     *           │
     *     ┌─────┴─────┐
     *     │           │
     * ┌───▼───┐   ┌───▼───┐
     * │   2   │   │   3   │
     * └───┬───┘   └───┬───┘
     *     │           │
     *     └─────┬─────┘
     *           │
     *       ┌───▼───┐
     *       │   4   │
     *       └───────┘
     */
    fn test_multiple_paths_to_origin() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (1, 3, RelType::ProviderToCustomer),
            (2, 4, RelType::ProviderToCustomer),
            (3, 4, RelType::ProviderToCustomer),
        ]);

        let (all_paths, _) = topo.propagate_paths(1, Direction::Up);

        dbg!(&all_paths);
        assert_eq!(all_paths.len(), 5);
        assert!(all_paths.contains(&vec![1]));
        assert!(all_paths.contains(&vec![1, 2]));
        assert!(all_paths.contains(&vec![1, 2, 4]));
        assert!(all_paths.contains(&vec![1, 3]));
        assert!(all_paths.contains(&vec![1, 3, 4]));
    }

    /*
     * Issue #4 test case
     * ┌────────┐     ┌────────┐       ┌───────┐
     * │  3356  ├─────┤  6453  │◄─────►│   3   │
     * └───┬────┘     └────┬───┘       └───────┘
     *     │               │
     *     └───────┬───────┘
     *             │
     *         ┌───▼───┐
     *         │   4   │
     *         └───────┘
     */
    #[test]
    fn test_works_in_any_provider_order() {
        let edges = vec![
            (3356, 6453, RelType::PearToPear),
            (3356, 3, RelType::PearToPear),
            (3356, 4, RelType::ProviderToCustomer),
            (6453, 4, RelType::ProviderToCustomer),
        ];

        let topo1 = Topology::from_edges(edges.clone());

        for _ in 0..10 {
            let topo2 = Topology::from_edges(edges.clone());

            if topo1.providers_of(4.into()) != topo2.providers_of(4.into()) {
                let (all_paths1, seen1) = topo1.propagate_paths(4, Direction::Up);
                let (all_paths2, seen2) = topo2.propagate_paths(4, Direction::Up);

                assert_eq!(all_paths1.len(), all_paths2.len());
                assert_eq!(seen1, seen2);
                assert!(seen1.contains(&3));
                assert!(seen2.contains(&3));
            }
        }
    }
}
