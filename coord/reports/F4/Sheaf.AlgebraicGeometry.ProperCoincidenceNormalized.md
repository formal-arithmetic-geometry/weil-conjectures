## What changed

Proved `AlgebraicGeometry.Etale.properCoincidence_exchange` in
`Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized`. The equality uses four proved
private helpers: factorization of derived identity isomorphisms on Qh, compatibility
of the derived identity-open adjunction with the formalism identity, cancellation
of identity-open base change, and refinement comparison of the pullback model with
the identity-open model. Invertibility uses the existing finite-ring proper base
change theorem. Added the proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison`.

All existing definitions, theorem signatures, visibility and public imports are
unchanged. Updated the node's proof and proof dependencies to describe the actual
argument. The unit's identity-open route is retained. The proof works for arbitrary
cartesian squares with proper f, including empty schemes, identity maps and the zero
coefficient ring; it introduces no nonemptiness, density, Noetherian or field
hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.properCoincidence_exchange`
(node `cor-cbc-proper-coincidence`). No holes remain in the item. Added 0 holes and
split off 0 statements. Every private helper is proved.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
The attached declaration of `def-compact-support-direct-image-detailed` constructs
the intrinsic unbounded pro-etale candidate; the present theorem already fixes the
ordinary etale bounded-below candidate and constructs its identity-open normalization.
No intrinsic-model bridge is used. Removed this node from proof dependencies while
retaining all statement dependencies.

Removed the redundant direct imports
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` and
`WeilConjectures.SixFunctors.BaseChange.Derived`; their declarations are still used
and available through the existing public `LowerShriekPlusBaseChange` import.

No application of `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion` or its
`thm-cbc-finite-torsion` theorem is needed: the ordinary proper theorem gives the
invertibility conjunct directly, as the original docstring permits. Its statement
dependency is unchanged. Neither public import is removed, and no module is
withdrawn. No claim is made that a removed direct import is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original DAG's single sentence omits two coherence checks required by the
specified Lean normalization: deriving the underived identity-open adjunction must
agree with the formalism shId, and the literal pullback compactification must be
compared with the identity-open one. Both are now proved locally from existing
source-library interfaces; no new assumed lemma or change of definitions was needed.
The original node proof also omitted the proper-base-change theorem needed for its
invertibility conclusion; it is now an explicit proof dependency. No statement is
disputed and no consumer adaptation or change record is required.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
