+++
id = "lemma-nagata-conrad-case3-smaller-base"
kind = "lemma"
title = "The smaller base in Case 3 (Conrad)"
order = 215
lean = ["AlgebraicGeometry.exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff"]
+++
Let $U\subseteq V$ be open subschemes of a scheme $X$ with $U$ quasi-compact,
and let $S\subseteq X$ be a quasi-compact subset disjoint from
$\overline{V\setminus U}$. There is a quasi-compact open subscheme
$X^{\circ}\subseteq X$ with $S\subseteq X^{\circ}$, $U\subseteq X^{\circ}$
and $X^{\circ}\cap V=U$.

## Proof

Since $V\setminus U$ is closed in $V$ we have
$\overline{V\setminus U}\cap V=V\setminus U$; in particular the open set
$W=X\setminus\overline{V\setminus U}$ contains $U$ and satisfies
$W\cap V=U$. It contains $S$ by hypothesis, so $S\cup U$ is a quasi-compact
subset of $W$. The underlying space of a scheme has a basis of quasi-compact
opens, so $S\cup U$ is contained in a quasi-compact open
$X^{\circ}\subseteq W$. Then $X^{\circ}\cap V\subseteq W\cap V=U$ and
$U\subseteq X^{\circ}\cap V$, so $X^{\circ}\cap V=U$.
