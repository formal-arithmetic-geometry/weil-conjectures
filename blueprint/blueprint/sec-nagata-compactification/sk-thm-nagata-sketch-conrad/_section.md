+++
id = "sk-thm-nagata-sketch-conrad"
kind = "section"
title = "Extension of a partial section after an admissible blow-up"
order = 202
uses = ["sk-def-nagata-sketch-quasidomination", "sk-lem-nagata-sketch-blowups", "sk-prop-nagata-sketch-zmt"]
lean = ["AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection"]
+++
*Theorem (sketch).*

Let $X,Y$ be qcqs $S$-schemes with $Y\to S$ separated and of finite
type. Let $U\subseteq V\subseteq X$ be dense quasi-compact opens,
and suppose $f:U\to Y$ quasi-dominates $V$ over $Y$.
There is a $V$-admissible blow-up $X'\to X$ and a quasi-domination
$f':W\to Y$ of $X'$ extending $f$.

## Proof

Replace $Y$ by $X\times_SY$ to regard $f$ as a partial section of
$Y\to X$. The four stages below are the elimination branch of the
diagram.

*Affine base, quasi-affine target, $U=V$.*
Over the affine base a quasi-affine target is a quasi-affine scheme, so
[sk-prop-nagata-sketch-zmt](ii) embeds it into relative affine space
(this affine-base case is the only form in which (ii) is used; the
later stages reduce to it by covering the base). Express the finitely
many coordinates of
$f$ on a finite principal-open cover of $U$. Clearing denominators
and blowing up the resulting finite-type ideal extends these coordinates
on an open of the blow-up with closed graph. Make $U$ scheme-theoretically dense, restrict to the inverse image of
an open in which the target is closed, and use schematic density to force
the extended coordinates to satisfy its defining ideal. The resulting
graph remains closed.

*Qcqs base, quasi-affine target, $U=V$.*
Carry out the affine construction on a finite affine cover of $X$.
Extend the local centres and take a common admissible refinement.
After making $U$ scheme-theoretically dense, the local extensions agree
where both are defined: their equalizer is closed by separatedness and
contains a scheme-theoretically dense open. They therefore glue.

*Quasi-affine target, $U\subseteq V$.*
Deligne's disjointness blow-up separates the closure of the section from
the inverse image of the closure of $V\setminus U$, using a centre
outside $V$. On its blow-up charts, one constructs a function vanishing on the
unwanted boundary closure and equal to $1$ on the section closure.
One can then work on a smaller quasi-compact open meeting $V$ exactly in
$U$, apply the preceding case there, and extend its centre to $X$.
The resulting blow-up preserves all of $V$.

*General target.*
Cover $Y$ by finitely many affine opens and apply the nested-open case
to the closures of the corresponding pieces of the partial section.
After a common $V$-admissible refinement, the closed graph over $X'$
has finite fibres and is quasi-finite. Zariski's Main Theorem makes
this graph quasi-affine over $X'$, reducing to the preceding case.
Composition of admissible blow-ups finishes the construction.

Uses: [sk-def-nagata-sketch-quasidomination], [sk-lem-nagata-sketch-blowups], [sk-prop-nagata-sketch-zmt]
