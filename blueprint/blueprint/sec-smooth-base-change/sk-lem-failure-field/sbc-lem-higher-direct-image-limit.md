+++
id = "sbc-lem-higher-direct-image-limit"
kind = "lemma"
title = "Higher direct images and limits of schemes"
order = 1389
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "sbc-lem-higher-direct-image-presheaf"]
+++
Let $S$ be a scheme and let
$X=\varprojlim_{i\in I}X_i$ be a limit of a directed system of schemes
over $S$ with affine transition morphisms, and assume the structure
morphisms $g_i:X_i\to S$ and $g:X\to S$ are
quasi-compact and
quasi-separated. Let $(\mathcal F_i)$ be a system of abelian sheaves
on $(X_i,f_{i'i})$, with $f_i:X\to X_i$ the projections, and set
$\mathcal F=\varinjlim_if_i^{-1}\mathcal F_i$. Then

$$
\varinjlim_{i\in I}R^pg_{i,*}\mathcal F_i
\xrightarrow{\ \sim\ }R^pg_*\mathcal F
$$

for every $p\geq0$.
(*Stacks Project, Lemma 59.51.7, [Tag `09Z1`](https://stacks.math.columbia.edu/tag/09Z1).*)

## Proof

By [sbc-lem-higher-direct-image-presheaf] both sides are
sheafifications of the presheaves $U\mapsto H^p(U\times_SX_i,\mathcal F_i)$ and $U\mapsto H^p(U\times_SX,\mathcal F)$ of
[def-weil-pbc-etale-cohomology]; for $U$ quasi-compact and
quasi-separated (e.g. affine) the colimit of the former is the latter
by continuity of etale cohomology under limits with affine transition
morphisms, and every object of $S_{\Et}$ has a covering by
quasi-compact quasi-separated objects, so the sheafifications agree.
