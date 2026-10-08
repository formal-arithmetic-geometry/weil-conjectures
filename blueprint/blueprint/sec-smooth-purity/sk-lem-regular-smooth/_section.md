+++
id = "sk-lem-regular-smooth"
kind = "section"
title = "A regular immersion of smooth schemes over a perfect field"
order = 2031
uses = ["sk-def-purity-conv"]
lean = ["AlgebraicGeometry.IsRegularImmersion.smooth_comp", "AlgebraicGeometry.IsRegularImmersion.ringKrullDim_stalk_add"]
+++
*Lemma (sketch).*

Let $i:Z\hookrightarrow X$ be a regular closed immersion of pure codimension
$c$, with $X$ smooth over the perfect field $k$ and $Z$ regular. Then both
structure morphisms $a_X:X\to\Spec k$ and $a_Z:Z\to\Spec k$ are smooth, and
$a_Z=a_X\circ i$. On a connected component of $X$ of dimension $n$, the
nonempty inverse image in $Z$ has pure dimension $m=n-c$.

## Proof

$X$ is smooth over $k$ by hypothesis. A regular finite-type scheme over a
perfect field is smooth over it (the regular–smooth criterion), so $a_Z$ is
smooth. Smooth schemes over a field are regular and their connected
components have a fixed dimension; on a component of $X$ of dimension $n$
the pure-codimension hypothesis gives dimension $n-c$ for each component of
$Z$ lying in it. The identity $a_Z=a_X\circ i$ is the definition of $i$ as a
$k$-morphism.

Uses: [sk-def-purity-conv]
