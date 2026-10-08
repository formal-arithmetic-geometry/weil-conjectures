+++
id = "lem-pc-cech-resolution"
kind = "lemma"
title = "The Cech resolution and derived direct image"
order = 670
uses = ["def-pc-derived-direct-image", "def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-morphism-hi", "lem-pc-affine-vanishing"]
+++
Let $S=\operatorname{Spec}(A)$, let $f:X\to S$ be a separated,
quasi-compact morphism, and choose a finite affine open cover
$X=\bigcup_{i=1}^t U_i$. For a quasi-coherent $\mathcal O_X$-module
$\mathcal F$, write $U_J=\bigcap_{j\in J}U_j$ and $j_J:U_J\to X$.
The augmented alternating Cech complex of sheaves

$$
0\longrightarrow\mathcal F\longrightarrow
\prod_i j_{i,*}(\mathcal F|_{U_i})\longrightarrow
\prod_{i<j}j_{ij,*}(\mathcal F|_{U_{ij}})\longrightarrow\cdots
$$

is exact. Its non-augmented terms are $f_*$-acyclic, so applying
$f_*$ to it computes $Rf_*\mathcal F$.

## Proof

Fix a point of $X$ and a covering open $U_i$ containing it.
Restrict the augmented complex to $U_i$. This restricted cover
contains the entire space $U_i$ as one member; insertion of that
index gives a contracting homotopy of the augmented Cech complex.
Thus the complex is locally exact, and hence exact as a complex
of sheaves. This argument does not identify a boundary stalk of
an open direct image with zero.

The intersections $U_J$ are affine: for two affine opens this follows
by pulling the closed diagonal of $X/S$ back to their affine
product over $S$, and the general case follows by induction.
Each $j_J$ is an affine morphism, since its inverse image in every
affine open of $X$ is again such an affine intersection.
By [lem-pc-affine-morphism-hi],
$R^qj_{J,*}(\mathcal F|_{U_J})=0$ for $q>0$.
For an affine open $V\subseteq S$, the inverse image
$U_J\times_S V$ is affine. The Leray spectral sequence for $j_J$
restricted over $V$, together with the preceding vanishing and
[lem-pc-affine-vanishing], gives

$$
H^q(f^{-1}V,j_{J,*}(\mathcal F|_{U_J}))
=H^q(U_J\times_S V,\mathcal F)=0\quad(q>0).
$$

Affine opens form a basis on $S$, so all higher direct images under
$f$ of these Cech terms vanish. A finite resolution by acyclic
objects computes the right derived functor (apply $f_*$ to an
injective double resolution and use its two spectral sequences).
This proves the assertion.
