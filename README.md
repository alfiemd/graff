# graff

A simple library for manipulating graphs.

The goal of this crate is to provide a flexible way to create and otherwise
manipulate graph structures. At this moment, the library is barebones, but
there is more to come. If you actually want to get things done for now, use
[petgraph](https://crates.io/crates/petgraph).

If you want the crate to be finished quicker, then you could consider
contributing. :)

## Examples

```rust
use graff::{Graph, GraphBehaviour, GraphError, EdgeDeleter, EdgePairAdder, VertexDeleter};
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut g = Graph::<i32>::with_vertices_and_edges(0..3, [(0,1), (1,2)])?;

    assert_eq!(g.vertex_count(), 3);
    assert_eq!(g.edge_count(), 2);

    g.add_vertices([3, 4]);
    g.add_edges([(1, 3),(2, 4)]);

    assert_eq!(g.vertex_count(), 5);
    assert_eq!(g.edge_count(), 4);

    // There are only five vertices, so edge is invalid.
    assert_eq!(g.add_edge((4, 5)), Err(GraphError::InvalidEdge));

    g.remove_edge((2, 4))?;
    assert_eq!(g.edge_count(), 3);

    g.add_vertices([6, 7]);

    // There is no vertex at index 7.
    assert_eq!(g.add_edge((6, 7)), Err(GraphError::InvalidEdge));
    // But we can add the edge by value instead.
    g.add_edge_by_vertices((6, 7))?;

    assert_eq!(g.edge_count(), 4);

    g.remove_edges([(0, 1), (1, 2)]);
    assert_eq!(g.edges().collect::<Vec<&(usize, usize)>>(), vec![&(1, 3), &(5, 6)]);

    g.remove_vertices([0, 1, 2, 3, 4]);
    assert_eq!(g.vertices().collect::<Vec<&i32>>(), vec![&6, &7]);

    // Removing the vertices above also removed their edges, and shifted the indices down
    assert_eq!(g.edges().collect::<Vec<&(usize, usize)>>(), vec![&(0, 1)]);
    Ok(())
}
```

## License

This project is released under [The Unlicense](https://unlicense.org/),
dedicated to the public domain.

## Contributing

Contributions welcome! :)

By submitting a pull request or otherwise contributing to this project, you
agree to dedicate your contribution to the public domain under the terms of
[The Unlicense](https://unlicense.org/), and you certify that you have the
right to do so.
