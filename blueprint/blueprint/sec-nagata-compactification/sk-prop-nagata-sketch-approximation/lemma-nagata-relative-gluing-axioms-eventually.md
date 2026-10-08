+++
id = "lemma-nagata-relative-gluing-axioms-eventually"
kind = "lemma"
title = "The relative gluing axioms hold at the selected stage"
order = 361
uses = ["def-nagata-relative-gluing-valid-stage", "lemma-nagata-directed-finite-upper-bound", "lemma-nagata-morphism-eq-eventually", "lemma-nagata-qc-open-eq-eventually", "lemma-nagata-relative-gluing-datum-descends"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

In $\mathsf R_{X,\lambda_{\mathrm{rel}}}$ the overlap opens match in both
directions, the overlap maps are inverse, and all triple-overlap cocycle
identities hold.

## Proof

Every required equality holds after base change to $S$. Equality of opens
and equality of morphisms therefore hold above their selected witness
stages. The common upper bound includes all finitely many pair and triple
conditions, so they hold simultaneously in the named datum.
