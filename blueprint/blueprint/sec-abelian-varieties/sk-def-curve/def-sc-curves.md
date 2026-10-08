+++
id = "def-sc-curves"
kind = "definition"
title = "Curves over algebraically closed fields"
lean = ["AlgebraicGeometry.IsCurve"]
order = 418
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $k$ be an algebraically closed field. A *curve over
$k$* is a separated scheme of finite
type over $k$ of dimension at most one; it is
*smooth* if it is smooth over $k$, *proper* if it is
proper over $k$, and *affine* if it is an affine scheme.
A *connected curve* is a curve that is nonempty, connected (as a
topological space) and of dimension one.
$\mathcal C$ denotes the category of smooth separated connected curves over
$k$.
(Here $k$ is required to be algebraically closed. A curve may be empty,
disconnected, or have zero-dimensional components; a statement that needs
a nonempty connected curve of dimension one says *connected curve*.
The Picard chapter also uses curves over arbitrary fields; its smooth
connected curves over algebraically closed fields are connected curves in
the present sense.)
