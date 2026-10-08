+++
id = "def-pc-proj"
kind = "definition"
title = "Projective spectrum and its standard opens"
order = 613
+++
For a nonnegatively graded commutative ring $S$, the scheme
$\operatorname{Proj}(S)$ has as points the homogeneous prime ideals
not containing $S_+$. Its standard open
$D_+(f)=\{\mathfrak p:f\notin\mathfrak p\}$, for homogeneous $f$
of positive degree, is the affine scheme $\operatorname{Spec}(S_{(f)})$;
the restriction maps are the graded localization maps.
Write $V_+(I)$ for the closed set of homogeneous primes containing $I$.
Here $\mathbf P^n_k=\operatorname{Proj}(k[x_0,\ldots,x_n])$, with
each $x_i$ of degree one.

*Mathlib:* `AlgebraicGeometry.Proj`, `AlgebraicGeometry.projIsoSpec`, `ProjectiveSpectrum.basicOpen`. These are basic Mathlib notions used throughout, so they are not mapped as the Lean declarations of this object.
