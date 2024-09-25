use crate::errors::GraphError;

/// A trait defining basic graph behaviour.
pub trait GraphBehaviour {
    /// A type representing a vertex.
    type Vertex;
    /// A type representing an edge.
    type Edge;
    /// A type identifying a vertex.
    type VertexId;
    /// A type identifying an edge.
    type EdgeId;

    /// Returns an iterator over the vertices of the graph.
    fn vertices(&self) -> impl Iterator<Item = &Self::Vertex>;

    /// Returns an iterator over the edges of the graph, each represented as a tuple of vertices.
    fn edges(&self) -> impl Iterator<Item = &Self::Edge>;

    /// Adds a vertex to the graph.
    fn add_vertex(&mut self, v: impl Into<Self::Vertex>);

    /// Adds an iterable of vertices to the graph.
    fn add_vertices(&mut self, vertices: impl IntoIterator<Item = impl Into<Self::Vertex>>) {
        for v in vertices {
            self.add_vertex(v);
        }
    }

    /// Adds an edge to the graph.
    ///
    /// # Errors
    ///
    /// Will return a [`GraphError`] error if it is trying to connect vertices that do not
    /// exist in the graph.
    fn add_edge(&mut self, e: impl Into<Self::Edge>) -> Result<(), GraphError>;

    /// Add an iterable of edges to the graph.
    ///
    /// # Errors
    ///
    /// Will return a [`GraphError`] if it is trying to connect vertices that do not exist in
    /// the graph.
    fn add_edges(
        &mut self,
        edges: impl IntoIterator<Item = impl Into<Self::Edge>>,
    ) -> Result<(), GraphError> {
        for e in edges {
            self.add_edge(e)?;
        }

        Ok(())
    }

    /// Attemps to remove a vertex from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the vertex to
    /// remove.
    fn remove_vertex_by_id(&mut self, v: impl Into<Self::VertexId>) -> Result<(), GraphError>;

    /// Remove an iterable of vertices from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find one of the vertices
    /// to remove.
    fn remove_vertices_by_id(
        &mut self,
        vertices: impl IntoIterator<Item = impl Into<Self::VertexId>>,
    ) -> Result<(), GraphError> {
        for v in vertices {
            self.remove_vertex_by_id(v)?;
        }

        Ok(())
    }

    /// Remove an edge from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the edge to remove.
    fn remove_edge_by_id(&mut self, e: impl Into<Self::EdgeId>) -> Result<(), GraphError>;

    /// Remove an iterable of edges from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find one of
    /// the edges to remove.
    fn remove_edges_by_id(
        &mut self,
        edges: impl IntoIterator<Item = impl Into<Self::EdgeId>>,
    ) -> Result<(), GraphError> {
        for e in edges {
            self.remove_edge_by_id(e)?;
        }

        Ok(())
    }

    /// Returns the number of vertices in the graph.
    fn vertex_count(&self) -> usize {
        self.vertices().count()
    }

    /// Returns the number of edges in the graph.
    fn edge_count(&self) -> usize {
        self.edges().count()
    }
}

/// A subtrait of for when it is possible to delete vertices without having to use
/// [`GraphBehaviour::VertexId`].
pub trait VertexDeleter: GraphBehaviour {
    /// Attemps to remove a vertex from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the vertex to
    /// remove.
    fn remove_vertex(&mut self, v: impl Into<Self::Vertex>) -> Result<(), GraphError>;

    /// Remove an iterable of vertices from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find one of the vertices
    /// to remove.
    fn remove_vertices(
        &mut self,
        vertices: impl IntoIterator<Item = impl Into<Self::Vertex>>,
    ) -> Result<(), GraphError> {
        for v in vertices {
            self.remove_vertex(v)?;
        }

        Ok(())
    }
}

/// A subtrait for when it is possible to delete vertices without having to use
/// [`GraphBehaviour::EdgeId`].
pub trait EdgeDeleter: GraphBehaviour {
    /// Remove an edge from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the edge to remove.
    fn remove_edge(&mut self, e: impl Into<Self::Edge>) -> Result<(), GraphError>;

    /// Remove an iterable of edges from the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find one of the edges to
    /// remove.
    fn remove_edges(
        &mut self,
        edges: impl IntoIterator<Item = impl Into<Self::Edge>>,
    ) -> Result<(), GraphError> {
        for e in edges {
            self.remove_edge(e)?;
        }

        Ok(())
    }
}

/// A subtrait for when it is possible to add edges between a pair of existing vertices directly by
/// their values.
pub trait EdgePairAdder: GraphBehaviour {
    /// Add an edge between two vertices of the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the vertices
    /// specified.
    fn add_edge_by_vertices(
        &mut self,
        from_to: (impl Into<Self::Vertex>, impl Into<Self::Vertex>),
    ) -> Result<(), GraphError>;

    /// Add an iterable of edges to the graph.
    ///
    /// # Errors
    ///
    /// This function will return a [`GraphError`] error if it cannot find the vertices
    /// specified.
    fn add_edges_by_vertices(
        &mut self,
        edges: impl IntoIterator<Item = (impl Into<Self::Vertex>, impl Into<Self::Vertex>)>,
    ) -> Result<(), GraphError> {
        for e in edges {
            EdgePairAdder::add_edge_by_vertices(self, e)?;
        }

        Ok(())
    }
}

/// A subtrait for when it is possible to search for vertices.
pub trait VertexSearcher: GraphBehaviour {
    /// Returns whether the graph contains the given vertex.
    fn contains_vertex(&self, v: impl Into<Self::Vertex>) -> bool;

    /// Returns whether the graph contains *all* of the given vertices.
    fn contains_vertices(
        &self,
        vertices: impl IntoIterator<Item = impl Into<Self::Vertex>>,
    ) -> bool {
        vertices.into_iter().all(|v| self.contains_vertex(v))
    }
}

impl<T> VertexSearcher for T
where
    T: GraphBehaviour,
    T::Vertex: PartialEq,
{
    fn contains_vertex(&self, v: impl Into<Self::Vertex>) -> bool {
        let v = v.into();
        self.vertices().any(|u| *u == v)
    }
}

/// A subtrait for when it is possible to search for edges.
pub trait EdgeSearcher: GraphBehaviour {
    /// Returns whether the graph contains the given edge.
    fn contains_edge(&self, e: impl Into<Self::Edge>) -> bool;

    /// Returns whether the graph contains *all* of the given edges.
    fn contains_edges(&self, edges: impl IntoIterator<Item = impl Into<Self::Edge>>) -> bool {
        edges.into_iter().all(|e| self.contains_edge(e))
    }
}

impl<T> EdgeSearcher for T
where
    T: GraphBehaviour,
    T::Edge: PartialEq,
{
    fn contains_edge(&self, e: impl Into<Self::Edge>) -> bool {
        let e = e.into();
        self.edges().any(|f| *f == e)
    }
}
