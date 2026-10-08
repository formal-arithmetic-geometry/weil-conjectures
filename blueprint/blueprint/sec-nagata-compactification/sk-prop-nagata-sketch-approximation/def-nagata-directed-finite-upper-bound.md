+++
id = "def-nagata-directed-finite-upper-bound"
kind = "definition"
title = "Selected upper bound of a finite set"
order = 328
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $I$ be a nonempty directed preorder. Fix a base point $i_\varnothing$
and, for each pair $(i,j)$, fix a selected common upper bound $d(i,j)$
together with proofs $i\leq d(i,j)$ and $j\leq d(i,j)$. Define
$u(F)\in I$ by Finset induction, inserting only an element $i\notin F$:

$$
u(\varnothing)=i_\varnothing,
\qquad
u(F\cup\{i\})=d(u(F),i)\quad(i\notin F).
$$
