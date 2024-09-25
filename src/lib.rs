#![deny(missing_docs)]
#![deny(unused_crate_dependencies)]

//! A simple library for manipulating graphs.
//!
//! At this moment, the library is barebones, but there is more to come. If you actually want to
//! get things done for now, use [petgraph](https://crates.io/crates/petgraph).
//!
//! See [`Graph`] for a quick start on some of the methods to manipulate graphs.
//!
//! # Example
//!
//! ```
//! # use graff::{Graph, GraphBehaviour, GraphError, EdgeDeleter, EdgePairAdder, VertexDeleter};
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let mut g = Graph::<i32>::with_vertices_and_edges(0..3, [(0,1), (1,2)])?;
//!
//! assert_eq!(g.vertex_count(), 3);
//! assert_eq!(g.edge_count(), 2);
//!
//! g.add_vertices([3, 4]);
//! g.add_edges([(1, 3),(2, 4)]);
//!
//! assert_eq!(g.vertex_count(), 5);
//! assert_eq!(g.edge_count(), 4);
//!
//! // There are only five vertices, so edge is invalid.
//! assert_eq!(g.add_edge((4, 5)), Err(GraphError::InvalidEdge));
//!
//! g.remove_edge((2, 4))?;
//! assert_eq!(g.edge_count(), 3);
//!
//! g.add_vertices([6, 7]);
//!
//! // There is no vertex at index 7.
//! assert_eq!(g.add_edge((6, 7)), Err(GraphError::InvalidEdge));
//! // But we can add the edge by value instead.
//! g.add_edge_by_vertices((6, 7))?;
//!
//! assert_eq!(g.edge_count(), 4);
//!
//! g.remove_edges([(0, 1), (1, 2)]);
//! assert_eq!(g.edges().collect::<Vec<&(usize, usize)>>(), vec![&(1, 3), &(5, 6)]);
//!
//! g.remove_vertices([0, 1, 2, 3, 4]);
//! assert_eq!(g.vertices().collect::<Vec<&i32>>(), vec![&6, &7]);
//!
//! // Removing the vertices above also removed their edges, and shifted the indices down
//! assert_eq!(g.edges().collect::<Vec<&(usize, usize)>>(), vec![&(0, 1)]);
//! # Ok(())
//! # }
//! ```

mod errors;
mod models;
mod traits;

pub use errors::*;
pub use models::*;
pub use traits::*;
