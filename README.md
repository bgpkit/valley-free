# Valley Free Explore

`valley-free` crate is a Rust package that reads CAIDA's [AS-relationship data][asrel]
and explores AS-level paths using `valley-free` model.

[asrel]: https://www.caida.org/data/as-relationships/

## Usage

### Rust

``` toml
[dependencies]
valley_free="0.2"
```

``` rust
use std::{fs::File, io::BufReader};
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

``` python
#!/usr/bin/env python3

import valley_free

topo = valley_free.load_topology("20161101.as-rel.txt.bz2")
paths = valley_free.propagate_paths(topo, 15169)

print(len(paths))
# 55483
```

## Build Python Package

Build for current Python environment:
`maturin build --release`

Build using manylinux environment:
`docker run --rm -v $(pwd):/io konstin2/maturin build`
