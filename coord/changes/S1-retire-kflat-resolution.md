# CochainComplex.exists_isKFlatResolution

## Reason

The retire-first item duplicates the proved upstream declaration and causes an import
collision. Retire the local duplicate and migrate every current direct importer.
Repair return C-32db9 (head `32db9440b4`): record and adapt the newly landed
`LowestResidueModelWithinOpen`. A further new consumer,
`RingedSpaceKFlatDirectImageHomLocalization`, is also included.
Repair return at head `6f46766ecf`: adapt and record all six named consumers.
The refreshed import audit also finds three new ringed derived comparison
consumers; adapt and record those in the same packet.
Repair the return at head `4f1871883`: record the additional transitive user
`Sheaf.Paper.SheafSliceDerivedComparison`. It already obtains the upstream theorem
through its existing imports, so its source and proved body require no adaptation.

## Old

```lean
theorem exists_isKFlatResolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (f : K ⟶ G), K.IsAcyclicTensorKFlat ∧ (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i))
```

## New

The declaration comes from the unchanged upstream module
`WeilConjectures.Algebra.Homology.KFlatResolution`:

```lean
theorem exists_isKFlatResolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (f : K ⟶ G), K.IsKFlatTensor ∧ (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i))
```

`IsKFlatTensor` and `IsAcyclicTensorKFlat` are definitionally equal, so all
hypotheses, universes and conclusions are preserved. Explicit K-flat imports
retain the original predicate API where used. No upstream source is edited.
Public consumer signatures stay unchanged; two existing long statement lines are
wrapped. In `ReductionPullFiniteEvaluation`, replace the private complex cube
lifting proof by a degreewise proof using the existing square API. Add the
proved private equation `mapComplexSquare_hom_f` and remove the now-unused
private `lift_complex_cube`. Mark `SheafOfModules.monoidalCategory` locally
irreducible. These changes avoid unfolding the full complex isomorphism while
checking the cube; no mathematical statement or dependency changes. The existing mathematical steps are preserved. The private `finite_model_abstract`
helper now takes normalization equations at its fixed representative rather
than four arbitrary predicates and universally quantified conditional equations.
Its caller obtains pullback K-flatness/flatness first and supplies exactly those
specialized equations. This preserves the public result and all source lemmas,
while reducing the type passed through the categorical pasting argument. The
original import-only consumer exceeded 60 seconds; the complete refactored
consumer compiled in 57.4 seconds before removing profiling and wrapping lines. The overlong public import in
`RingedToposDerivedPushforwardComposition` uses the shorter upstream
`GrothendieckAbelian` module, which publicly re-exports the original module.

In `NilpotentReductionStep`, full-set validation reached a 60-second timeout.
Change the private `cancellationComplexIso`, `coefficientTensorIso`, and
`leftDerived_model` from data definitions into proved `Nonempty` theorems.
Their callers obtain the comparisons inside proofs; no canonical comparison
is needed by the public result. Unpack the proof fields of the already chosen
extension functor once in `reduction_model`, retaining the exact chosen functor
and derived scalar extension. Scope monoidal irreducibility to the private
additivity proof. The complete module compiles cleanly in 42.0 seconds.
This preserves public signatures and every mathematical step and adds no hole.

In `CompletionUnitFiniteProjection`, add the proved private `limit_counit_app`
component equation and use the existing mapped-complex component lemmas in
`ordinary_projection_unit`, avoiding a large definitional conversion. Obtain
its realization isomorphism as a `Nonempty` witness inside the transport proof,
and identify the completion composite explicitly. Keep `constantSheaf` and
`HasDerivedCategory.standard` locally irreducible to avoid expanding their data.
The public theorem and its mathematical argument are unchanged. The isolated
ordinary finite-unit checks improved from 37.3 to 17.3 seconds. The complete
proof then checked in 33.1 seconds; the reported unused simp argument and
redundant tactic sequencing are removed before delivered-set validation.

The current base has independently retired eight former consumers, including
`DerivedPullback` and `DerivedPullbackTensorAssociativity`; their stale sandbox
copies are omitted. Current upstream pullback imports and the current
`IsKFlatTensor` signatures in the counit-adjustment consumer are preserved.
The node attachment for `lem-pc-kflat-resolution` already points to the
independent-coefficient theorem. Only a stale module name in another node proof
is updated. No target statement or definition changes.

Repair return C-69276 (head `69276862f`): drop the sandbox restorations of the
quarantined relatively-flat twins and their node overrides. They have separate
rework assignments and are not required to retire this resolution module.
Drop the stale tensor-counit override, its node override and its proposed reuse
record; preserve M4's landed compatibility re-export and adopted node attachment.
Keep all 35 current importer migrations and the private proof refactors above.

The duplicate canonical model's existing data definitions exceeded 60 seconds.
Its six definitions already exist upstream with identical constructions and
definitionally equal signatures. Keep its original import path as a compatibility
re-export, retaining the public Sheaf pullback-comparison API. The exact old/new
text and all users are recorded in
`coord/changes/S1-canonical-derived-tensor-hom-model-reuse.md`.
Repoint `def-pc-canonical-derived-tensor-hom-model` to that adopted module with
`existing: true` and the verbatim adopted declaration signature.

The finite-evaluation proof also keeps `HasDerivedCategory.standard` and
`constantSheaf` locally irreducible and obtains its final realization via a
proved `Nonempty` witness. The private `flatOnSite_iff` and `pullback_kflat_bridge`
check the abstract flatness transport before concrete specialization. All these
helpers are proved in the same module; no dependency or hole is added.

The C-69276 validation again reached 60 seconds in the finite-evaluation
consumer. Profiling narrowed the cost to concrete comparison specialization.
The proved private `legacy_kflat` helper checks the definitional equality of
`IsKFlatTensor` and `IsAcyclicTensorKFlat` once for an abstract coefficient sheaf;
the final resolution argument applies this conversion explicitly. Scope
transparency-respecting elaboration to `flatOnSite_iff` and
`pullback_kflat_bridge`, retaining the existing setting for the concrete cast
proof. The complete unprofiled module compiles cleanly in 43.1 seconds, with
unchanged public signature and no additional hole or import.

## Users

Current source audit (2026-10-22): all 35 direct importers have sandbox
adaptations. With the canonical-model compatibility module, the packet contains
36 Lean modules. Every current declaration user and adapted module is recorded
below; the model's additional users are in its separate change record. The two
quarantined relatively-flat modules are recorded as preserved separate rework,
not restored or adapted. The landed tensor-counit re-export is unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AcyclicKFlatTensor | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.DerivedChangeOfRings | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.KFlatResolution | S1 | Retire duplicate; use the proved upstream theorem. |
| Sheaf.Algebra.Homology.KFlatTensorQuasiIso | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.NilpotentDerivedUpperBound | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.SiteDerivedTensorDescent | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | Reuse the six identical adopted definitions through the same import path; all model users are recorded separately in S1-canonical-derived-tensor-hom-model-reuse.md. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Replace only the direct resolution proof import; preserve the complete proof and public signature. Wrap one overlong private-helper line. |
| Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange | unclaimed | Remove the unused resolution proof import; preserve its statement and existing proof hole. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | A4; quarantined | Separate rework assignment; source, archive and node preserved without restoration or adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | rework-hold; quarantined | Separate rework assignment; source, archive and node preserved without restoration or adaptation. |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | unclaimed | Preserve the landed adopted-theorem re-export, docstring and existing:true node attachment; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.LocalKFlatTensorRoof | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.CategoryTheory.RingedToposDerivedAdjunctionOfUniverses | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.CompletionUnitFiniteProjection | unclaimed | Replace the resolution import; use explicit counit component equations and an abstract realization witness in the transport proof; preserve public signatures. |
| Sheaf.Paper.ConstantCompletionUnitNormalization | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.NilpotentReductionStep | unclaimed | Replace the resolution import; use proved private comparison-existence interfaces and unpack derived-functor proof fields once; preserve public signatures. |
| Sheaf.Paper.ReductionPullFiniteEvaluation | unclaimed | Replace the direct resolution import; use the degreewise square API and keep monoidal and standard derived-category structures locally irreducible for compilation; preserve public signatures. |
| Sheaf.Paper.RestrictionDerivedProducts | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.RingedProjectionTensorStructure | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.RingedSliceDerivedAdjunction | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.RingedTopoiDerivedPullback | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.Paper.SheafSliceDerivedComparison | unclaimed | Transitive user of the resolution theorem; existing imports provide the unchanged upstream declaration after migration. Preserve current source and proved body without adaptation. |
| Sheaf.SixFunctors.RingedDerivedAdjointLift | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.SixFunctors.RingedDerivedCompositionComparison | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.SixFunctors.RingedDerivedIdentityComparison | unclaimed | Replace the direct resolution import; preserve current signatures and proof bodies. |
| Sheaf.SixFunctors.RingedDerivedTwoIsoComparison | unclaimed | Already proved independently and no longer imports the retired module; preserve current source without adaptation. |

## Status

landed 20261022T025340-L-1290470 2026-10-22 (merge of deliver/S1/Sheaf.Algebra.Homology.KFlatResolution)
