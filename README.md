# Valley Free Explorer

`valley-free` crate is a Rust package that reads CAIDA's [AS-relationship data][asrel]
and explores AS-level paths using `valley-free` model.

[asrel]: https://www.caida.org/data/as-relationships/

## Core Ideas

### Topology Building

The first step for doing `valley-free` paths simulation is to obtain AS-level
topology and inter-AS relationships. Here in this library, we utilize CAIDA's
[AS-relationship data][asrel] data to obtain both the AS relationships and the
topology.

The CAIDA's AS-relationship data is formatted as follows:
```
## A FEW LINES OF COMMENT
## A FEW LINES OF COMMENT
## A FEW LINES OF COMMENT
1|7470|0
1|9931|-1
1|11537|0
1|25418|0
2|35000|0
2|263686|0
...
```

The data format is:
```example
<provider-as>|<customer-as>|-1
<peer-as>|<peer-as>|0
```

A non-comment row in the dataset means:
- there is a AS-level link between the two ASes
- the relationships are either peer-to-peer (0) or provider-to-customer (-1)

### Path Propagation

Instead of finding paths from traffic sources to origins ASes, it simulates
the AS paths propagation from the origins and recording all the paths the
propagation reaches. For example, when searching for all potential paths toward
AS15169, it starts from as15169 on the topology, and find all next hops that
conform with valley-free routing (i.e. the path with the next hop is still
valley-free), and then recursively doing depth-first search until no more
valley-free-conforming next hops can be found. As a result, the paths should
contain all possible paths toward an asn.

The simluation is recursively done for each given origin ASN. Recursion breaking
conditions are:
1. loop detected;
2. previously propagated from the AS;
3. all **valid next-hop** ASes have been propagated

**Valid next-hops** are determined as follows:
1. if the current path is propagated from a customer, then it can
propagate to all of its' customers, providers, and peers;
2. if the current path is propagated from a provider or a peer, it can
only propagate to its customers.

## Usage

### Rust

``` toml
[dependencies]
valley_free="0.2"
```

``` rust
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
```

### Python

The package is available on PyPi at https://pypi.org/project/valley-free/. For installation, `pip3 install valley-free`
should do the trick.

``` python
#!/usr/bin/env python3

import valley_free

topo = valley_free.load_topology("20161101.as-rel.txt.bz2")
paths = valley_free.propagate_paths(topo, 15169)

print(len(paths))
# 117074
```

#### Manually build Python package 

Build for current Python environment:
`maturin build --release --features py`

Build using manylinux environment:
`docker run --rm -v $(pwd):/io konstin2/maturin build --release --features py`
