+++
id = "cor-picard-degree-g"
kind = "theorem"
title = "The degree of the dictionary"
order = 745
uses = ["def-pc-degree-line-bundle", "def-pc-euler-characteristic", "def-pc-smooth-projective-curve", "lem-pc-curves-are-sc", "lem-pc-genus-base-change", "lem-sc-riemann-roch"]
tags = ["latex:corollary"]
lean = ["AlgebraicGeometry.Scheme.degree_eq_genus"]
+++
Let $X$ be a smooth projective curve ([def-pc-smooth-projective-curve])
which is geometrically irreducible, hence geometrically integral with
$H^0(X,\cO_X)=k$ (this is needed: for $X=\mathbf P^1_{\mathbf C}$ over
$k=\mathbf R$ and $K=\mathbf C$ the conclusion fails),
of genus $g$ and $\cL$ a line
bundle on $X_K$ ($K/k$ any field extension) with $h^0(X_K,\cL)=1$
and $H^q(X_K,\cL)=0$ for $q>0$. Then

$$
\deg(\cL)=\chi(\cL)-\chi(\cO_{X_K})=1-(1-g)=g.
$$

This is the exact instance of Riemann–Roch used in the
zero-scheme dictionary ([lem-pc-zero-scheme-recd]).

## Proof

The vanishing gives $\chi(\cL)=h^0=1$ ([def-pc-euler-characteristic]).
Riemann–Roch [lem-sc-riemann-roch], applied to $\cO$ after the flat
base change to $\bar K$ (which changes neither $\chi(\cO)$ nor the
genus, [lem-pc-genus-base-change], whose hypotheses "geometrically
irreducible with $H^0(X,\cO_X)=k$" are the ones assumed here; the
smooth projective curve
$X_{\bar K}$ over the algebraically closed field $\bar K$ is a proper
smooth connected curve in the sense of that lemma by
[lem-pc-curves-are-sc], $X_{\bar K}$ being integral because $X$ is
geometrically integral), gives $\chi(\cO_{X_K})=1-g$; and
$\deg\cL=\chi(\cL)-\chi(\cO_{X_K})$ by [def-pc-degree-line-bundle].
Hence $\deg\cL=g$.

Uses: [def-pc-degree-line-bundle], [def-pc-euler-characteristic], [def-pc-smooth-projective-curve], [lem-pc-curves-are-sc], [lem-pc-genus-base-change], [lem-sc-riemann-roch]
