/// Represents errors that can occur during various graph operations, such as removing a vertex
/// that does not exist.
///
/// # Example
///
/// ```
/// # use graff::{Graph, GraphError, VertexDeleter, GraphBehaviour, EdgeDeleter};
/// let mut g = Graph::<i32>::with_vertices(1..4);
///
/// // Cannot remove 0 since it is not a vertex.
/// assert_eq!(g.remove_vertex(0), Err(GraphError::VertexNotFound));
///
/// // But we can remove the element with id 0, which for [`Graph`] means the vertex at index 0.
/// assert!(g.remove_vertex_by_id(0usize).is_ok());
///
/// // The vertex set is now `[2,3]`.
/// assert_eq!(g.vertices().collect::<Vec<&i32>>(), vec![&2, &3]);
///
/// // There is no vertex with index 2.
/// assert_eq!(g.remove_vertex_by_id(2usize), Err(GraphError::VertexIdInvalid));
///
/// // There are no vertices with those indices.
/// assert_eq!(g.remove_edge((3, 5)), Err(GraphError::InvalidEdge));
///
/// // There *are* vertices with those indices, but the edge is not present in the graph.
/// assert_eq!(g.remove_edge((0, 1)), Err(GraphError::EdgeNotFound));
///
/// // There are no edges in the graph!
/// assert_eq!(g.remove_edge_by_id(0usize), Err(GraphError::EdgeIdInvalid));
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum GraphError {
    /// Indicates an attempt to access a [`crate::traits::GraphBehaviour::Vertex`] that does
    /// not exist.
    VertexNotFound,
    /// Indicates an attempt to access an [`crate::traits::GraphBehaviour::Edge`] that does not
    /// exist.
    EdgeNotFound,
    /// Indicates if the [`crate::traits::GraphBehaviour::Edge`] is not properly formed.
    InvalidEdge,
    /// Indicates if the [`crate::traits::GraphBehaviour::VertexId`] does not exist.
    VertexIdInvalid,
    /// Indicates if the [`crate::traits::GraphBehaviour::EdgeId`] is invalid.
    EdgeIdInvalid,
}

impl std::fmt::Display for GraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GraphError::VertexNotFound => write!(f, "vertex could not be found"),
            GraphError::EdgeNotFound => write!(f, "edge could not be found"),
            GraphError::InvalidEdge => write!(f, "such an edge cannot be built"),
            GraphError::VertexIdInvalid => write!(f, "no vertex has that id"),
            GraphError::EdgeIdInvalid => write!(f, "no edge has that id"),
        }
    }
}

impl std::error::Error for GraphError {}
