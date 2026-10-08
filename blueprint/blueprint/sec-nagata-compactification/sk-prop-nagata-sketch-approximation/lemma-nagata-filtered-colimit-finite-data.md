+++
id = "lemma-nagata-filtered-colimit-finite-data"
kind = "lemma"
title = "Finite data and finite relations descend in a filtered colimit"
order = 331
uses = ["lemma-nagata-directed-finite-upper-bound"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $(A_i)_{i\in I}$ be a directed system of rings with colimit $A$. Given
finitely many elements of $A$ and finitely many equalities between ring
expressions in those elements, there exists one stage $i$ and lifts of all
selected elements to $A_i$ for which all selected equalities hold. Once
they hold at $i$, they hold after every transition $A_i\to A_j$.

## Proof

Choose a representative stage for each selected element. Directedness and
[lemma-nagata-directed-finite-upper-bound] place all representatives at
one common stage. Equality of two representatives in a filtered colimit is
witnessed at a later stage. There are only finitely many equalities, so a
second finite upper bound makes them all true simultaneously. Ring
homomorphisms preserve the equalities at every later stage.
