+++
id = "prop-constructible-generic-constancy"
kind = "theorem"
title = "Generic constancy"
order = 1170
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_dense_open", "AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_openCover", "Topology.Stratification.dense_iUnion_interior_stratum"]
tags = ["latex:proposition"]
uses = ["def-constructible-constant", "def-constructible-constructible", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-constructible-stratification", "def-kun-separably-closed", "lemma-constructible-immersion-independence", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-locally-constant", "lemma-openclosed-stalk-upperstar", "prop-constructible-pullback"]
+++
Let $X$ be a scheme and let $\mathcal F\in\shv{\et X}$ be constructible.
Then there is a dense open $U\subseteq X$ such that $\mathcal F|_U$ is
finite locally constant. (No Noetherian hypothesis on $X$ is needed.)

## Proof

Let $(\iota_k\colon Z_k\to X)_{k<n}$ be a stratification witnessing
constructibility, with strata $X_k=\iota_k(Z_k)$, and let
$U=\bigcup_kU_k$ with $U_k$ the interior of $X_k$ in $X$.

*$U$ is dense.* A locally closed subset $L$ of a topological space
with empty interior is nowhere dense: writing $L=V\cap\overline L$ with $V$
open, the open set $\operatorname{int}\overline L$ meets $V$ inside
$\operatorname{int}L=\emptyset$, and an open subset of $\overline V$
disjoint from $V$ is empty. A finite union of nowhere dense sets is
nowhere dense (if $A$ is closed with empty interior and $B$ has empty
interior, then $\operatorname{int}(A\cup B)\setminus A$ is an open subset
of $B$, hence empty, so $\operatorname{int}(A\cup B)\subseteq \operatorname{int}A=\emptyset$). Now $X_k\setminus U_k$ is locally closed
with empty interior, so $N=\bigcup_k(X_k\setminus U_k)$ is nowhere dense,
and $X\setminus N\subseteq U$ since the $X_k$ cover $X$; the complement of
a set with empty interior is dense, hence so is $U$.

*$\mathcal F|_U$ is finite locally constant.* The open subsets
$U_k$ cover $U$, and $\mathcal F|_{U_k}$ is the pullback of $\mathcal F$
along the open immersion $U_k\to X$, whose image $U_k$ is contained in
$X_k=\iota_k(Z_k)$; since $\iota_k^*\mathcal F$ is finite locally
constant, so is $\mathcal F|_{U_k}$ by
[lemma-constructible-immersion-independence] (in the form: for an
immersion $b$ and any morphism $a$ with image in the image of $b$,
$b^*\mathcal F$ finite locally constant implies $a^*\mathcal F$ finite
locally constant). Finally, a sheaf which is finite locally constant on
each member of an open cover is finite locally constant: the trivialising
étale covers of the restrictions compose to a trivialising étale
cover, and a geometric point of $U$ lifts to a member of the open cover
containing its image, where the stalk is unchanged.
