## What changed

Replaced the already-proved finite discrete branch
`AlgebraicGeometry.ProEtale.finiteCoefficient_serreHeart_cohomology_vanishes`
by a direct étale-origin argument. Its public signature and all existing public
imports are unchanged. A private coefficient-lift isomorphism transports the
small finite ring into the scheme universe.

Added `Sheaf.Paper.FiniteDiscreteSerreHeartCd`, proving
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteDiscrete_serreHeart_cohomology_vanishes`.
The normalized ordinary encoding transports the weak Serre coproduct hull to
ordinary sheaves of étale origin. The common ℓ-power annihilator makes the étale
antecedent torsion, so the assumed étale dimension bounds its cohomology. Derived
sections comparison and exact scalar forgetting give vanishing for natural
q > d. The existing finite branch follows, with its original integer q > d+2.
This avoids any ind-constructible presentation or finite-complex-heart estimate.

Updated the finite-branch node's proof dependencies and the main node's proof
audit to match this argument. No existing statement, definition or source-library
module changes. No forced adaptations or withdrawals.

Validation: the two-module sandbox compile passed after unused-import cleanup.
The required delivery runs the final compiler and axiom checks. Existing public signatures and public
imports were compared verbatim with the current shared source.

## Proved and sorry left

Item holes before: 1. Item holes closed: 0. Item holes after: 1. New holes: 0.
This is dependency pruning and a proved stronger finite-coefficient lemma, not a
proof or decomposition of the unrestricted topological theorem.

The remaining `sorry` is
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
(node `lem-sfb-torsion-cd-topological-serre-transfer`). Its signature and proof
status remain unchanged. The other five coefficient alternatives still require
an arbitrary-affine weak Serre cohomological estimate.

The new finite-discrete theorem and all its private helpers have complete proofs.
The existing finite-coefficient theorem has a complete replacement proof.
Zero rings, empty schemes and d = 0 require no exclusions: all torsion and
comparison arguments apply to these cases as stated.

## No longer needed

Removed the item's private proof imports
`Sheaf.Paper.TorsionCdIndFiniteHeart` and
`Sheaf.Paper.FiniteCoefficientSerreIndHeart`. The finite branch no longer uses
nodes `lem-sfb-torsion-cd-ind-finite-heart` or
`lem-sfb-finite-coefficient-serre-ind-heart` (the corresponding imported
presentations and bound are replaced by étale-origin comparison).

Import-closure comparison from `TargetsCheck` removes these seven modules:

- `Sheaf.Paper.CondensedSectionsIndVanishing`
- `Sheaf.Paper.ConstructibleFiniteHeart`
- `Sheaf.Paper.FiniteCoefficientSerreIndHeart`
- `Sheaf.Paper.FiniteConstructibleComplexHeartCd`
- `Sheaf.Paper.FiniteConstructibleComplexHeartPresentations`
- `Sheaf.Paper.FiniteDiscreteSerreIndConstructible`
- `Sheaf.Paper.TorsionCdIndFiniteHeart`

In the item's import closure alone, these five additional project modules also
fall out (other target paths still import them):

- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Sheaf.SixFunctors.ExistsFiniteRefinementTree`
- `Sheaf.SixFunctors.SchemeRefinementTree`
- `Sheaf.SixFunctors.SchemeRefinementTreeEncoding`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`

No module is deleted. In particular, the unresolved main node retains its
conditional finite-heart/Noetherian proof audit and corresponding DAG dependencies;
this pruning does not assert that those mathematical obligations have been
withdrawn. `FiniteConstructibleComplexHeartCd` has a hole, now absent from this
finite-branch Lean proof. The ledger, rather than this local comparison, determines
net target-closure progress.

## Where the brief, the DAG or earlier work was wrong

The finite branch need not use the general finite-complex-heart estimate. Its
coefficients are finite discrete, and the exact comparison essential image is
already weak Serre and coproduct closed. Thus the hypothesis on X itself gives
the stronger bound q > d directly.

STATEMENT-DISPUTED remains at the unrestricted theorem: the original structural
approximation step was refuted on arbitrary affine schemes, and its repaired
statement requires Noetherianity. The counterexample concerns approximation,
not this vanishing conclusion. The Noetherian specialization and the finite
branch do not cover all coefficient alternatives of the unchanged theorem.
HRS Section 8, condition (8.1) and Lemma 8.6 do not state the full arbitrary-affine
weak Serre assertion, and their algebraic-extension colimit topology must not
replace the all-continuous norm topology in the algebraic-closure alternative.
The supported derived-generation hull has all integer shifts; its membership
alone cannot supply this numerical upper bound.

## New nodes

`lem-sfb-finite-discrete-serre-heart-cd` records the fully proved normalized finite
discrete coefficient bound. It is strictly the finite-coefficient part of the
argument, has no new `sorry`, uses only the bound on X, and gives q > d. Its proof
steps record normalized encoding, constructible étale origin, weak Serre closure
via exact fully faithful comparison and its derived extension closure, torsion
étale cohomology, and derived evaluation comparison. No change record is needed:
no existing interface or definition changes.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
