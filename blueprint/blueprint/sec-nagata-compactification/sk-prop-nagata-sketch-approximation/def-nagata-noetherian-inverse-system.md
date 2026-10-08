+++
id = "def-nagata-noetherian-inverse-system"
kind = "definition"
title = "Noetherian approximation"
order = 340
lean = ["AlgebraicGeometry.Scheme.NoetherianApproximation"]
+++
A *Noetherian approximation* of a scheme $S$ consists of a cofiltered
index category $I_S$, a diagram $\lambda\mapsto S_\lambda$ of schemes of
finite type over $\mathbf Z$ whose transition morphisms
$t_{\mu\lambda}\colon S_\mu\to S_\lambda$ are affine, together with a limit
cone over that diagram with vertex $S$, so that

$$
S=\varprojlim_{\lambda\in I_S}S_\lambda .
$$

We write $\mathsf N(S)=(I_S,(S_\lambda)_\lambda, (t_{\mu\lambda})_{\lambda\leq\mu})$ for such a system. Each stage
$S_\lambda$ is then a Noetherian scheme, by the Hilbert basis theorem. The
construction of the following subsection produces such a system for every
quasi-compact quasi-separated $S$, by gluing the affine case
([lemma-nagata-noetherian-inverse-system-affine]) over a finite affine
cover.
