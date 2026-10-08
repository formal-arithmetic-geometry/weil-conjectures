+++
id = "lemma-nagata-relative-proj-invertible-tensor-powers"
kind = "lemma"
title = "Proj of the tensor powers of an invertible ideal"
order = 109
uses = ["def-nagata-invertible-ideal", "def-nagata-relative-proj", "lemma-nagata-relative-proj-exists", "lemma-nagata-relative-proj-invertible-tensor-powers-affine"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

If $\mathcal L$ is an invertible ideal on $Y$, the relative Proj of
$\bigoplus_{n\geq0}\mathcal L^{\otimes n}$ is canonically isomorphic to $Y$.
Under this isomorphism $\mathcal O(1)$ identifies with $\mathcal L$, and
the universal degree-one map $\mathcal L\to\mathcal O(1)$ is the identity
of $\mathcal L$. The inclusion
$\mathcal L\hookrightarrow\mathcal O_Y$ is a separate effective-Cartier
inclusion and is not the tautological quotient.

## Proof

Cover $Y$ by affine opens $V$ on which $\mathcal L$ has a generator $a$.
By [lemma-nagata-relative-proj-invertible-tensor-powers-affine], the
relative Proj restricts over each such $V$ to $V$, with the identification
induced by the degree-zero localization map. On an overlap $V\cap W$, if
$b=ua$ for a unit $u$, the two chart identifications send a fraction
$(r a^n)/a^n$ (respectively $(r u^{-n}b^n)/b^n$) to the same coefficient $r$.
Hence they agree on overlaps and glue, by the relative-Proj gluing
compatibility, to a canonical isomorphism with $Y$. The degree-one
localization identifies the tautological section with the chosen generator;
these local identifications glue to $\mathcal O(1)\cong\mathcal L$, and the
resulting universal degree-one map is the identity on $\mathcal L$. The
inclusion $\mathcal L\hookrightarrow\mathcal O_Y$ is independent of this
tautological quotient and remains the specified effective-Cartier inclusion.
