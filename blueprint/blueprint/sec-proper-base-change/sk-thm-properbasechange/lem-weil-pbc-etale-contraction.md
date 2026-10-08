+++
id = "lem-weil-pbc-etale-contraction"
kind = "lemma"
title = "Strict henselian local rings in the etale contraction"
order = 1227
uses = ["def-weil-pbc-etale-contraction", "def-weil-pbc-henselian-terminology", "def-weil-pbc-ind-etale-algebra", "lem-weil-pbc-etale-finite-data-descent", "lem-weil-pbc-ind-etale-stability"]
+++
The map $R\to R^{\mathrm e}$ is faithfully flat and ind-etale
[def-weil-pbc-ind-etale-algebra]. Every faithfully flat etale algebra of
finite presentation over $R^{\mathrm e}$ has a section. Every maximal
localization of $R^{\mathrm e}$ is strictly henselian
[def-weil-pbc-henselian-terminology].

## Proof

Finite tensor products in [def-weil-pbc-etale-contraction] are faithfully
flat and etale. Their transition maps are faithfully flat, so tensoring a
nonzero module into their filtered colimit never kills a nonzero element.
Consequently all the stated colimit maps are faithfully flat; they are
ind-etale by [lem-weil-pbc-ind-etale-stability]. An etale algebra of finite
presentation over $R^{\mathrm e}$ descends to some $R_n$, and a surjective
etale covering of finite presentation descends after increasing $n$, by
[lem-weil-pbc-etale-finite-data-descent]. Its algebra occurs as a tensor
factor in $R_{n+1}$. The resulting map from that algebra to $R^{\mathrm e}$
is the required section.

Put $S=R^{\mathrm e}$ and let $\mathfrak m$ be maximal. An affine etale
neighbourhood of the closed point of $\operatorname{Spec}S_{\mathfrak m}$
descends, after clearing finitely many denominators, to an affine etale map
$E\to\operatorname{Spec}S$ whose image contains $D(f)$ for some
$f\notin\mathfrak m$. Choose $a\in S$ with $g=1-af\in\mathfrak m$. The finite
etale family $E\amalg\operatorname{Spec}S_g\to\operatorname{Spec}S$ is
surjective and has a section by the preceding paragraph. After localization
at $\mathfrak m$, a section lands in a single summand, since a local ring has
no nontrivial idempotent. It cannot land in $S_g$, since $g\in\mathfrak m$.
Thus every such etale neighbourhood has a local section.

For clarity, the elementary local-ring criterion just used to recognize
strict henselianity consists of two tests. A finite separable residue
extension can be lifted by a monic polynomial with invertible derivative to
an etale neighbourhood. Its section forces that residue extension to be
trivial. Similarly an approximate simple root of a monic polynomial defines
an etale neighbourhood after inverting its derivative. Shrink this
neighbourhood to exclude the other points of its finite closed fibre; its
section then lifts the specified root. The simple-root Hensel criterion,
equivalently lifting idempotents of finite algebras, is the henselian
condition of [def-weil-pbc-henselian-terminology]. Together these tests prove
strict henselianity.
