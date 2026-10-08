+++
id = "prop-weil-pbc-common-stage-calculus"
kind = "theorem"
title = "Common-stage additive and shift calculus"
order = 1309
uses = ["def-weil-pbc-finite-stage-pair-category", "prop-weil-pbc-scalar-extension"]
tags = ["latex:proposition"]
+++
The equivalence relation of [def-weil-pbc-finite-stage-pair-category] is
reflexive, symmetric, and transitive. Transport is additive and obeys
$(u_N)_P=u_P$ for $M\subset N\subset P$. The common-stage operations are
representative-independent and make $\mathcal P_T$ an additive category.
Every finite diagram of objects, morphisms, composites, and asserted
equalities in $\mathcal P_T$ is represented over one finite field, and an
asserted equality holds exactly when it holds after passage to a further
common stage.

Define
$$
 (E,K)[1]=(E,K[1])
$$
and, for $f=[M,u]:(E,K)\to(F,L)$, define
$$
 f[1]=\left[M,
 \sigma_{M/F,L}^{-1}\circ u[1]\circ\sigma_{M/E,K}\right].
$$
This gives a well-defined additive autoequivalence $[1]$ with inverse
$[-1]$, and every finite-stage inclusion
$j_E:\mathcal C_E(T)\to\mathcal P_T$ commutes with shifts through the
specified comparison.

*Source note:* no Stacks Project entry states this form: the ledger's
verified entries contain no filtered-colimit category, and the blueprint
adds the common-stage calculus, in which every finite diagram and every
asserted equality in $\mathcal P_T$ is represented over one finite
coefficient field. The nearest entries, each fetched and quoted, are
Definition 4.21.1 ([Tag 00D3](https://stacks.math.columbia.edu/tag/00D3),
the directed-set condition satisfied by the poset $\mathsf{FinExt}_\ell$)
and Lemma 4.21.5 ([Tag 0032](https://stacks.math.columbia.edu/tag/0032))
with Remark 4.21.6 ([Tag
09P8](https://stacks.math.columbia.edu/tag/09P8)). Difference: Stacks
computes the colimit of a diagram in one fixed category, whereas the colimit
here indexes a category, so addition, composition, shifts and finitely many
asserted equalities must first be transported to one common stage.

## Proof

The relation of [def-weil-pbc-finite-stage-pair-category] is reflexive and
symmetric from the definitions, and transitive: if $(M,u)\sim(N,v)$ and
$(N,v)\sim(Q,w)$ with witnesses $P_1,P_2$, transport all to their compositum
$P$, where both equalities hold by the transport formula $(u_N)_P=u_P$ and
the unit/associator equations of [prop-weil-pbc-scalar-extension]. The same
formula shows that transport is additive and satisfies $(u_N)_P=u_P$ for
$M\subset N\subset P$ (the associator cocycle), so addition, negatives,
identities and composition, computed after transport to one common finite
field, are independent of the representatives and of the field; the
finite-stage additive category laws transported to a common field (with
$T_{F/E}$ additive) make $\mathcal P_T$ an additive category. Every finite
diagram is represented over one finite field by transporting objects and
morphisms (via the $\gamma$-isomorphisms of
[def-weil-pbc-finite-stage-pair-category]), and a finite list of asserted
equalities holds in $\mathcal P_T$ exactly when the transported equalities
hold over a further common stage, by the definition of the equivalence. For
the shift: equivalent representatives define equivalent shifted
representatives by naturality of $\sigma$ and the associator equations of
[prop-weil-pbc-scalar-extension], so $[1]$ and $[-1]$ are well-defined
additive endofunctors, $[1]$ has inverse $[-1]$ (the finite-stage shift
laws), and the inclusion $j_E$ commutes with the shifts through the
specified comparison.
