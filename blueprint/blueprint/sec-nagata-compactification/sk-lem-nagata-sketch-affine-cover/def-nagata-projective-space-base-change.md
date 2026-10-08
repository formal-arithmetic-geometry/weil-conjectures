+++
id = "def-nagata-projective-space-base-change"
kind = "definition"
title = "Projective space over a base scheme, by base change"
order = 307
lean = ["AlgebraicGeometry.ProjectiveSpace"]
uses = ["def-nagata-affine-proj"]
+++
Let $n$ be a finite index set and $S$ a scheme. Put

$$
\mathbf P^n_{\mathbf Z}
=\operatorname{Proj}\bigl(\mathbf Z[T_i:i\in n]\bigr),
\qquad
\mathbf P(n;S)
=S\times_{\operatorname{Spec}\mathbf Z}\mathbf P^n_{\mathbf Z},
$$

where the polynomial ring carries its total-degree grading, and take for the
structural morphism $\mathbf P(n;S)\to S$ the first projection. Here $n$
indexes the *homogeneous* coordinates, so the classical
$\mathbf P^r_S$ is $\mathbf P(\{0,\dots,r\};S)$.

This is the same scheme over $S$ as
[def-nagata-relative-projective-space], but obtained without any
gluing, so it does not come with the standard-chart interface required
there; only the properties of $\mathbf P(n;S)$ as a scheme over $S$ are
available from it. In particular it gives no way to construct morphisms
*into* $\mathbf P(n;S)$; the route does not need such morphisms.
