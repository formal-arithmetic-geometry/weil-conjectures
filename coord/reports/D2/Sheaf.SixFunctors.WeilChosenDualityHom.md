## What changed

Proved `WeilConjectures.SfWeilChosenDuality.chosen_duality_hom` from the recorded
`coef_verdier_weil_equivariance` conclusion. Private constructions transport an
actual carrier functor to fixed pairs along a natural isomorphism, apply internal
Hom to a dualizing-object isomorphism, lift equivariant biduality, and transport
that biduality. The coefficient unit and canonical dualizing identification come
from the dependency's `DualizingNormalization`; the lifted adjunction retains the
actual unit and counit. For a chosen right adjoint, the comparison is exactly
`adj.rightAdjointUniq adjCan` at the coefficient unit. Full faithfulness gives the
bijection with forward map precisely `f ↦ V.map f.op`.

Added proof-only imports of the existing `IsoAlgebraAdjunction` and
`IsoAlgebraTwist` modules. Updated the owning node's proof, proof dependencies,
and proof origin to match these constructions. All existing declaration
signatures, public definitions, public imports and docstrings are preserved.
No new public declaration or node, definition repair, or consumer adaptation.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.SfWeilChosenDuality.chosen_duality_hom`
(`lem-sf-weil-chosen-duality-hom`). Added zero holes; zero holes remain in the
item module. The full proof compiled in 23.1 seconds. Style-only cleanup replaced
`haveI` with `have` and unnecessary tactic sequencing; delivery validation follows. This is a proof from the published dependency declarations, whose
own unfinished proofs remain their separate items.

## No longer needed

Removed the proof-only direct import
`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` and removed
`lem-fix-weil-operations` from this node's proof dependencies. The recorded
coefficient data already supply the dual structure, its biduality equivariance,
and the exceptional mate. Naturality and conjugation construct the specified
Hom lifts without the mixed-support cup-product declaration attached to that
node. No upstream declaration or module is withdrawn, and no claim is made that
this removes the module from every other target's import closure.

The other original dependencies remain used. The existing closed
`lem-sf-fixed-pair-adjunction-lift` is now cited explicitly for the literal
lifted adjunction and carrier unit/counit equations; it is a categorical tool
with the exact mate hypotheses already supplied by `Z.common`.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The old `lem-fix-weil-operations` Lean
attachment names `isWeilPairing_mixedSupportCupProduct`, which is not the
categorical internal-Hom lifting API suggested by the prose plan. The owning
coefficient-equivariance conclusion already contains the data needed here.
The finite Hom-identification fields of `B` supply the full common-stage Hom
pair predicate directly at the compositum, so no separate constructibility or
isomorphism-invariance lemma has to be introduced.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
