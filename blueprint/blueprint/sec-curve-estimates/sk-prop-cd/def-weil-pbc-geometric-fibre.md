+++
id = "def-weil-pbc-geometric-fibre"
kind = "definition"
title = "Geometric fibre of a finite morphism"
order = 995
lean = ["AlgebraicGeometry.Scheme.Hom.GeometricFiber"]
+++
Let $h:W\to V$ be a morphism and let $\bar v:\operatorname{Spec}\Omega\to V$ be a
geometric point with $\Omega$ algebraically closed. The *geometric fibre* of $h$
over $\bar v$ is the set of morphisms $\bar w:\operatorname{Spec}\Omega\to W$ with
$h\circ\bar w=\bar v$; equivalently, the set of $\Omega$-points of the scheme-theoretic
fibre $W\times_V\operatorname{Spec}\Omega$. It is finite when $h$ is finite.
