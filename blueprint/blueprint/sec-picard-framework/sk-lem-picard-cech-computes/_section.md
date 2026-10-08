+++
id = "sk-lem-picard-cech-computes"
kind = "section"
title = "Leray's theorem for quasi-coherent sheaves"
order = 609
uses = ["sk-def-av-jacobian", "sk-lem-picard-affine", "sk-thm-picard-cech"]
lean = ["AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_homology_iso_H"]
+++
*Lemma (sketch).*

Let $X$ be separated over an affine base $S=\Spec A$ and let
$\mathfrak U$ be an open affine covering. Then for every quasi-coherent
$\cO_X$-module $\cF$ the edge map of [sk-thm-picard-cech] is an
isomorphism of $A=\Gamma(S,\cO_S)$-modules

$$
\Cech^q(\mathfrak U,\cF)\overset{\sim}{\longrightarrow}H^q(X,\cF)
\qquad(q\ge0);
$$

in particular it is $k$-linear when $S=\Spec k$.

## Proof

*Step 1 (the intersections are affine).* For two affine opens
$U,V\subseteq X$ the intersection $U\cap V$ is the preimage of $U\times V$
under the diagonal of $X$; separatedness makes the diagonal a closed
immersion, and $U\times V$ is affine over the affine base, so $U\cap V$
is a closed subscheme of an affine scheme, hence affine. Iterating,
every $U_{i_0\dots i_p}=U_{i_0}\cap\dots\cap U_{i_p}$ is affine.

*Step 2 (the spectral sequence collapses).* Feed $\mathfrak U$ to
[sk-thm-picard-cech]. For $q>0$ the presheaf $\mathcal H^q(\cF)$
vanishes on each $U_{i_0\dots i_p}$ by Step 1 and
[sk-lem-picard-affine], so $E_2^{p,q}=\Cech^p(\mathfrak U,\mathcal H^q(\cF))=0$ for $q>0$. Only the row $q=0$ survives, the
sequence degenerates, and the edge maps
$\Cech^q(\mathfrak U,\cF)\to H^q(X,\cF)$ are isomorphisms in every
degree; this is the collapse described in Step 4 of the proof of
[sk-thm-picard-cech].

*Step 3 (linearity).* Both sides are $A$-modules through
$A\to\Gamma(X,\cO_X)$, an element $a\in A$ acting by functoriality
through the endomorphism $a\cdot\colon\cF\to\cF$ of $\cO_X$-modules;
the spectral sequence of [sk-thm-picard-cech], hence its edge map,
is natural in $\cF$, so the edge map commutes with these endomorphisms
and is $A$-linear.

This is Stacks, Cohomology of Schemes, Lemma 30.2.6
([`01XD`](https://stacks.math.columbia.edu/tag/01XD)); the detailed form is Blueprint 50,
`lem-pc-cech-computes`.

Uses: [sk-lem-picard-affine], [sk-thm-picard-cech]
