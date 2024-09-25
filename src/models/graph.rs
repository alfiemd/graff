use crate::errors::GraphError;
use crate::{EdgeDeleter, EdgePairAdder, GraphBehaviour, VertexDeleter};

/// A barebones representation of a graph.
///
/// # Quick start
///
/// ## Adding vertices
///
/// - [`GraphBehaviour::add_vertex`] is all you need.
///
/// ## Removing vertices
///
/// - [`VertexDeleter::remove_vertex`] will remove a vertex matching the vertex you supply.
/// - [`GraphBehaviour::remove_vertex_by_id`] will remove the vertex at the index you specify.
///
/// ## Adding edges
///
/// - [`GraphBehaviour::add_edge`] will add an edge given a pair of (vertex) indices.
/// - [`EdgePairAdder::add_edge_by_vertices`] will add an edge given a pair of vertices.
///
/// ## Removing edges
///
/// - [`EdgeDeleter::remove_edge`] will remove an edge given a pair of (vertex) indices.
/// - [`Graph::swap_remove_edge`] will swap remove an edge given a pair of (vertex) indices; this
///     will *not* preserve the edge ordering.
/// - [`GraphBehaviour::remove_edge_by_id`] will remove the edge at the given index.
/// - [`Graph::swap_remove_edge_by_id`] will swap remove the edge at the given index; this will
///     *not*
///     preserve the edge ordering.
/// - [`Graph::remove_edge_by_vertices`] will remove an edge given a pair of vertices.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Graph<T> {
    /// The vertices of the graph.
    vertices: Vec<T>,
    /// The edges of the graph, stored as pairs of indices.
    edges: Vec<(usize, usize)>,
}

impl<T> Default for Graph<T> {
    /// Creates a default instance of [`Graph`] with empty vertex set and edge set, where each
    /// vertex has type `T` ([`GraphBehaviour::Vertex`]).
    ///
    /// # Example
    ///
    /// ```
    /// # use graff::{Graph, GraphBehaviour};
    /// // Each vertex in our graph has type `usize`.
    /// let g = Graph::<usize>::default();
    /// assert_eq!(g.vertex_count(), 0);
    /// assert_eq!(g.edge_count(), 0);
    /// ```
    fn default() -> Self {
        Graph {
            vertices: vec![],
            edges: vec![],
        }
    }
}

impl<T> Graph<T> {
    /// Returns an empty graph.
    #[must_use]
    pub fn new() -> Graph<<Graph<T> as GraphBehaviour>::Vertex> {
        Graph::default()
    }

    /// Returns an edgeless graph with the vertex set provided.
    pub fn with_vertices(
        vertices: impl IntoIterator<Item = impl Into<<Graph<T> as GraphBehaviour>::Vertex>>,
    ) -> Graph<T> {
        Graph {
            vertices: vertices.into_iter().map(Into::into).collect(),
            edges: vec![],
        }
    }

    /// Creates a new instance of [`Graph`] given iterables that can be converted into vertices
    /// [`GraphBehaviour::Vertex`] and edges [`GraphBehaviour::Edge`].
    ///
    /// # Example
    ///
    /// ```
    /// # use graff::{Graph, GraphBehaviour};
    /// let g = Graph::<i32>::with_vertices_and_edges([1,2,4], [(0,1), (1,2)]).unwrap();
    /// assert_eq!(g.vertex_count(), 3);
    /// assert_eq!(g.edge_count(), 2);
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if one of the edges cannot be added, such as when it is trying to join
    /// two vertices that do not exist in the graph.
    pub fn with_vertices_and_edges(
        vertices: impl IntoIterator<Item = impl Into<<Graph<T> as GraphBehaviour>::Vertex>>,
        edges: impl IntoIterator<Item = impl Into<<Graph<T> as GraphBehaviour>::Edge>>,
    ) -> Result<Graph<T>, GraphError> {
        let mut g = Graph::with_vertices(vertices);

        for e in edges {
            <Graph<T> as GraphBehaviour>::add_edge(&mut g, e)?;
        }

        Ok(g)
    }
}

impl<T> GraphBehaviour for Graph<T> {
    /// The [`GraphBehaviour::Vertex`] here is the generic type `T` of [`Graph<T>`].
    type Vertex = T;
    /// The [`GraphBehaviour::Edge`] here stores the index pairs of (adjacent) vertices.
    type Edge = (usize, usize);
    /// The [`GraphBehaviour::VertexId`] here is the index of the vertex stored in the
    /// collection.
    type VertexId = usize;
    /// The [`GraphBehaviour::EdgeId`] here is the index of the vertex stored in the
    /// collection.
    type EdgeId = usize;

    fn vertices(&self) -> impl Iterator<Item = &Self::Vertex> {
        self.vertices.iter()
    }

    fn edges(&self) -> impl Iterator<Item = &Self::Edge> {
        self.edges.iter()
    }

    fn add_vertex(&mut self, v: impl Into<Self::Vertex>) {
        self.vertices.push(v.into());
    }

    fn add_edge(&mut self, e: impl Into<Self::Edge>) -> Result<(), GraphError> {
        let (from, to) = e.into();
        if from >= self.vertices.len() || to >= self.vertices.len() {
            return Err(GraphError::InvalidEdge);
        }

        self.edges.push((from, to));

        Ok(())
    }

    fn remove_vertex_by_id(&mut self, v: impl Into<Self::VertexId>) -> Result<(), GraphError> {
        let index = v.into();

        if index >= self.vertex_count() {
            return Err(GraphError::VertexIdInvalid);
        }

        self.vertices.remove(index);

        self.edges
            .retain(|&(from, to)| from != index && to != index);

        for edge in &mut self.edges {
            if edge.0 > index {
                edge.0 -= 1;
            }
            if edge.1 > index {
                edge.1 -= 1;
            }
        }

        Ok(())
    }

    fn remove_edge_by_id(&mut self, e: impl Into<Self::EdgeId>) -> Result<(), GraphError> {
        let index = e.into();

        if index >= self.edge_count() {
            return Err(GraphError::EdgeIdInvalid);
        }

        self.edges.remove(index);

        Ok(())
    }
}

impl<T: PartialEq> VertexDeleter for Graph<T> {
    fn remove_vertex(&mut self, v: impl Into<Self::Vertex>) -> Result<(), GraphError> {
        let v = v.into();

        if let Some(index) = self.vertices.iter().position(|u| u == &v) {
            self.vertices.remove(index);

            self.edges
                .retain(|&(from, to)| from != index && to != index);

            for edge in &mut self.edges {
                if edge.0 > index {
                    edge.0 -= 1;
                }
                if edge.1 > index {
                    edge.1 -= 1;
                }
            }

            return Ok(());
        }

        Err(GraphError::VertexNotFound)
    }
}

impl<T> EdgeDeleter for Graph<T> {
    fn remove_edge(&mut self, e: impl Into<Self::Edge>) -> Result<(), GraphError> {
        let e = e.into();
        let (u, v) = e;

        if u >= self.vertices.len() || v >= self.vertices.len() {
            return Err(GraphError::InvalidEdge);
        }

        if let Some(index) = self.edges.iter().position(|&f| f == e) {
            self.edges.remove(index);
            return Ok(());
        }

        Err(GraphError::EdgeNotFound)
    }
}

impl<T: PartialEq> EdgePairAdder for Graph<T> {
    fn add_edge_by_vertices(
        &mut self,
        from_to: (impl Into<Self::Vertex>, impl Into<Self::Vertex>),
    ) -> Result<(), GraphError> {
        let (u, v) = from_to;
        let u = u.into();
        let v = v.into();

        if let Some(from) = self.vertices.iter().position(|x| *x == u) {
            if let Some(to) = self.vertices.iter().position(|x| *x == v) {
                self.edges.push((from, to));
                return Ok(());
            }
        }
        Err(GraphError::VertexNotFound)
    }
}

impl<T: PartialEq> Graph<T> {
    /// Remove an edge from the graph without preserving the ordering.
    ///
    /// # Errors
    ///
    /// Returns a [`GraphError`] error if the edge cannot be removed, such as when it is
    /// referring to vertex indices that do not exist.
    pub fn swap_remove_edge(
        &mut self,
        e: impl Into<<Graph<T> as GraphBehaviour>::Edge>,
    ) -> Result<(), GraphError> {
        let e = e.into();
        let (u, v) = e;

        if u >= self.vertices.len() || v >= self.vertices.len() {
            return Err(GraphError::InvalidEdge);
        }

        if let Some(index) = self.edges.iter().position(|&f| f == e) {
            self.edges.swap_remove(index);
            return Ok(());
        }

        Err(GraphError::EdgeNotFound)
    }

    /// Remove an iterable of edges from the graph without preserving the ordering.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find one of the edges to
    /// remove.
    pub fn swap_remove_edges(
        &mut self,
        edges: impl IntoIterator<Item = impl Into<<Graph<T> as GraphBehaviour>::Edge>>,
    ) -> Result<(), GraphError> {
        for e in edges {
            self.swap_remove_edge(e)?;
        }

        Ok(())
    }

    /// Remove an edge from the graph without presering the ordering.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError::EdgeIdInvalid`] error if it cannot find one of
    /// the edges to remove.
    pub fn swap_remove_edge_by_id(
        &mut self,
        e: impl Into<<Graph<T> as GraphBehaviour>::EdgeId>,
    ) -> Result<(), GraphError> {
        let index = e.into();

        if index >= self.edge_count() {
            return Err(GraphError::EdgeIdInvalid);
        }

        self.edges.swap_remove(index);

        Ok(())
    }

    /// Remove an iterable of edges from the graph without presering the ordering.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError::EdgeIdInvalid`] error if it cannot find one
    /// of the edges to remove.
    pub fn swap_remove_edges_by_id(
        &mut self,
        edges: impl IntoIterator<Item = impl Into<<Graph<T> as GraphBehaviour>::EdgeId>>,
    ) -> Result<(), GraphError> {
        for e in edges {
            self.swap_remove_edge_by_id(e)?;
        }

        Ok(())
    }

    /// Remove an edge given a pair of vertices.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError::EdgeNotFound`] if there is no such edge in
    /// the graph.
    pub fn remove_edge_by_vertices(
        &mut self,
        e: (
            impl Into<<Graph<T> as GraphBehaviour>::Vertex>,
            impl Into<<Graph<T> as GraphBehaviour>::Vertex>,
        ),
    ) -> Result<(), GraphError> {
        let (u, v) = e;
        let u = u.into();
        let v = v.into();

        for (i, (from, to)) in self.edges.iter().enumerate() {
            if self.vertices[*from] == u && self.vertices[*to] == v {
                self.edges.remove(i);
                return Ok(());
            }
        }

        Err(GraphError::EdgeNotFound)
    }
}
