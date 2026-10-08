+++
id = "sbc-lem-bc-injectivity"
kind = "lemma"
title = "Injectivity of the critical map and its cokernel"
order = 1384
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "lemma-weil-pbc-five-lemma-transfer", "lemma-weil-pbc-leray-acyclicity", "sbc-def-base-change-map", "sbc-def-base-change-property", "sbc-lem-bc-naturality"]
+++
With $f:X\to S$ and $n$ as in [sbc-def-base-change-property], assume for
some $q\geq1$ that $\mathrm{BC}(f,n,q-1)$ holds universally (in the
single degree $q-1$; no hypothesis in the degrees $<q-1$ is needed).
Let $S'\to S$ be a morphism, $f':X'=X\times_SS'\to S'$ the base change,
$g:T\to S'$ a quasi-compact and quasi-separated morphism, and
$h:Y=X'\times_{S'}T\to X'$, $e:Y\to T$ the projections. Then for
every abelian sheaf $\mathcal F$ on $T_{\Et}$ annihilated by $n$:

1. the base-change map
$f'^{-1}R^qg_*\mathcal F\to R^qh_*e^{-1}\mathcal F$ is
injective;
1. if $\mathcal F\subset\mathcal G$ with $\mathcal G$ annihilated by
$n$, then
$$
\operatorname{Coker}\bigl(f'^{-1}R^qg_*\mathcal F\to
R^qh_*e^{-1}\mathcal F\bigr)
\subset\operatorname{Coker}\bigl(f'^{-1}R^qg_*\mathcal G\to
R^qh_*e^{-1}\mathcal G\bigr);
$$
1. if in (2) the sheaf $\mathcal G$ is an injective sheaf of
$\mathbf Z/n\mathbf Z$-modules, then
$$
\operatorname{Coker}\bigl(f'^{-1}R^qg_*\mathcal F\to
R^qh_*e^{-1}\mathcal F\bigr)
\subset R^qh_*e^{-1}\mathcal G.
$$

(*Stacks Project, Lemma 59.88.2, [Tag `0F03`](https://stacks.math.columbia.edu/tag/0F03).*)

## Proof

Choose a short exact sequence
$0\to\mathcal F\to\mathcal I\to\mathcal Q\to0$ with $\mathcal I$ an
injective sheaf of $\mathbf Z/n\mathbf Z$-modules on $T_{\Et}$. The
injective-acyclicity input of [lemma-weil-pbc-leray-acyclicity]
(using the adjunction of [def-weil-pbc-inverse-image]) gives
$R^qg_*\mathcal I=0$ for $q>0$, so the two long exact sequences of
higher direct images of [def-weil-pbc-direct-image] (in the
derived categories of [def-weil-pbc-derived-categories], the
distinguished triangle of the short exact sequence) and the naturality
of the base-change maps of [sbc-def-base-change-map] ([sbc-lem-bc-naturality]) give the
diagram with exact rows of the statement: the long exact sequences are
the ones of [lemma-weil-pbc-five-lemma-transfer]; the left two
vertical arrows are the degree-$(q-1)$ base-change maps for
$\mathcal I$ and $\mathcal Q$ for the base change $f'$ along $g$, hence
isomorphisms by $\mathrm{BC}(f',n,q-1)$, which is part of the
hypothesis that $\mathrm{BC}(f,n,q-1)$ holds universally (only this
single degree enters), the top
right entry $f'^{-1}R^qg_*\mathcal I$ is zero, hence the middle vertical arrow is injective,
which is (1), and the same diagram gives the inclusion of the cokernel
into $R^qh_*e^{-1}\mathcal I$, which is (3); for (2), with
$\mathcal F\subset\mathcal G\subset\mathcal I$, the same diagram
applied to $\mathcal F\subset\mathcal G$ gives the inclusion of the
cokernels.
