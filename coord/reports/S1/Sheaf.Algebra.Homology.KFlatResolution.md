## What changed

Retire the zero-hole duplicate `Sheaf.Algebra.Homology.KFlatResolution` and migrate
all 35 current direct importers to the proved adopted theorem (or remove their
unused import). Retain explicit legacy K-flat imports where needed. Preserve
public consumer signatures and the previously delivered private proof refactors
in `ReductionPullFiniteEvaluation`, `NilpotentReductionStep`, and
`CompletionUnitFiniteProjection`. Their proved component and existence APIs avoid
expanding concrete comparison constructions. No adopted source file is changed.

Repair every point of return C-69276, reviewed head `69276862f`:

- H4/A1: omit the sandbox restorations of
  `RelativelyFlatDerivedBaseChangeComplex` and `RelativelyFlatTensorBaseChangeIso`,
  and omit their two node overrides. Preserve their quarantine archives, current
  records and separate rework assignments.
- B: omit the stale `TensorCounitOneKFlatCoordinates` source and node overrides.
  Withdraw the proposed `S1-tensor-counit-one-kflat-reuse.md` from this packet.
  Preserve M4's landed re-export, docstring and existing adopted node attachment.
- G6: retain the `CanonicalDerivedTensorHomModel` compatibility re-export and
  include `def-pc-canonical-derived-tensor-hom-model`, repointed to
  `WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel` with
  `existing: true` and the adopted declaration signature verbatim. Its semantic
  statement, dependencies and proof records stay unchanged.

The retained packet contains 36 Lean modules and two node updates. The other
node update replaces a stale resolution-module reference in a proof step of
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`. The resolution node
already points to the independent-coefficient theorem and needs no update.
Current source comparisons retain the landed consumer proofs; the required
`deliver3.py` rebases the packet onto the fetched current branch.

Change records:
`coord/changes/S1-retire-kflat-resolution.md` and
`coord/changes/S1-canonical-derived-tensor-hom-model-reuse.md`.
All current resolution declaration users and adapted consumers are listed in the
first record; all six canonical-model declaration users are in the second.

## Proved and sorry left

Assigned item: 0 of 0 holes closed; 0 holes added; 0 split off. This is a
retirement and compatibility repair, not a new mathematical proof.
`CochainComplex.exists_isKFlatResolution` remains fully proved upstream; its
`IsKFlatTensor` conclusion is definitionally equal to the legacy predicate.

The three existing consumer holes are unchanged:

- `SheafOfModules.wf_site_derived_tensor_descent`
  (`lem-weil-pbc-site-derived-tensor-descent`).
- `CategoryTheory.RingedDerivedComparisons.identityComparison_exists`
  (`lem-sfb-ringed-derived-identity-comparison`).
- `AlgebraicGeometry.schemeInternalHom_baseChange_exchange`
  (`lem-sc-internal-hom-base-change-exchange`).

## No longer needed

Withdraw only `lean/Sheaf/Algebra/Homology/KFlatResolution.lean` via `deleted.txt`.
All 35 direct importers cease importing it. `InternalHomBaseChangeExchange` needs
no replacement resolution import. The duplicate private helpers `flat_of_iso`,
`flat_small_coproduct` and `flat_terms_mappingCone` disappear with that module;
its upstream counterpart and all upstream dependencies remain untouched.
The finite-evaluation proof no longer needs private `lift_complex_cube`.
The canonical-model compatibility module re-exports its six adopted definitions
instead of repeating their identical constructions; its original public
pullback-comparison API remains available. No new mathematical dependency is
introduced and no DAG node is deleted.

Do not restore independently retired consumers: `DerivedOpenPullbackHomology`,
`DerivedPullback`, `DerivedPullbackCompositionCoherence`,
`DerivedPullbackCompositionIsIso`, `DerivedPullbackTensorAssociativity`,
`IsomorphismPullbackCounit`, `RelativeTensorPullbackHomologyComparison`,
`SingleComplexBaseChangeStalkCondition`, or `AffineDerivedPullbackTensorTilde`.
`RingedDerivedTwoIsoComparison` and `StrictPerfectTensorRelativeTorBound` already
ceased importing the duplicate and need no adaptation.
The relatively-flat twins remain quarantined for their own assignments; this
packet does not withdraw them or remove their dependencies.

## Where the brief, the DAG or earlier work was wrong

The returned packet incorrectly restored two quarantined twins that duplicate
live adopted declarations and are not needed by this retirement. It also
included stale tensor-counit edits that would undo M4's landed source and node
record, and omitted the canonical-model adopted attachment. These errors are
repaired explicitly above. Only the assigned resolution retirement remains in
`deleted.txt`; dropped sandbox overrides are not library deletion requests.

The repaired full-set compile passed its first 22 modules, then reached the
60-second limit in `ReductionPullFiniteEvaluation`. Diagnostic prefix checks
and profiling isolated repeated concrete normalization of the two definitionally
equal K-flat predicate spellings in the final specialization. Add the proved
private `legacy_kflat` conversion with abstract coefficients, and invoke it at
that specialization. Scope transparency-respecting elaboration to the existing
`flatOnSite_iff` and `pullback_kflat_bridge` helpers, preserving the concrete
module-pullback cast proof's existing setting. The complete unprofiled module
then compiles cleanly in 43.1 seconds. All diagnostic modules were removed from
the delivered Lean set; no development options remain.

The prior import migrations required proof-only normalization refactors to meet
the existing per-file limit. Those refactors remain intact, with all helpers
proved and no proof split into another file. This repair preserves current
public signatures, target meanings and the unit route.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
