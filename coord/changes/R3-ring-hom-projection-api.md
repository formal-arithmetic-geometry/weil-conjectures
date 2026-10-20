# CategoryTheory.ringHomComplexProjection

## Reason

The completed adjacent calculation needs a folded specification of the chosen
Hom-complex projections. Directly exposing `homComplex_exists.choose_spec` makes
conversion unfold the large bifunctor witness; a repair compile using this route
exceeded the 60-second single-file limit. The existing upstream theorem
`homComplex_projections_exists` states the identical existential specification with
`homComplexFunctor` folded. Use this interface in the definition and its proof API.

This repairs the returned packet at `ca57320f6a`: its import named the retired
`Sheaf.Algebra.Homology.HomComplexProjections`. The current source module is
`WeilConjectures.Algebra.Homology.HomComplexProjections`, which publicly imports
`WeilConjectures.Algebra.Homology.HomComplex`.

Both existential proofs are proofs of the same proposition. Proof irrelevance makes
their chosen projection data definitionally equal once the chosen functor is exposed.
The public signature and the value of the projection therefore stay the same.
All other shared definitions and public signatures remain unchanged. No target's
meaning changes. No source-library declaration, signature or import is edited.

## Old

Public import: `WeilConjectures.Algebra.Homology.HomComplex`.

```lean
noncomputable def ringHomComplexProjection {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X p) (Q.X (p + n)) :=
  (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
    P Q n p (p + n) rfl
```

## New

Public import: `WeilConjectures.Algebra.Homology.HomComplexProjections`.

```lean
noncomputable def ringHomComplexProjection {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X p) (Q.X (p + n)) :=
  (homComplex_projections_exists (R := CochainComplex.onePointRingSheaf A)).choose
    P Q n p (p + n) rfl
```

The item also uses local irreducibility attributes for `homComplexFunctor` and
`ringExtensionPure` after establishing its private pure-tensor API. They affect
only elaboration within the item and do not change exported reducibility attributes.

## Users

The table is the complete current `tools/downstream.py
Sheaf.Algebra.Homology.RingHomExtensionDefs --uses ringHomComplexProjection` list,
including the shared module. All consumers keep the same statements because the
projection type and chosen value are unchanged; none needs a source adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.BoundedAboveCoherentRHom | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.NilpotentDerivedUpperBound | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.NormalizedRingHomExtension | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingDualTermFlat | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomScalarExtension | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeIsIso | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap | H3 | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition | V1 | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPrecomposition | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.RingExtensionInternalHomExt | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.RingHomExtensionDefs | unclaimed | Definition repair; same chosen projections. |
| Sheaf.Algebra.Homology.RingHomExtensionDegrees | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Algebra.Homology.RingHomExtensionDifferential | R3 | Proved adjacent calculation with folded projection specification. |
| Sheaf.Algebra.Homology.RingHomExtensionTransport | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.FunctorialRingComplexDescentData | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.FunctorialRingComplexIdealDescent | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.FunctorialRingComplexSheaf | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexCechBaseChange | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexCechData | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexGodementConstruction | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexGodementFunctorial | D5 | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexGodementModelMaps | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingComplexSemilinearExtension | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingFamilyLocallyEqualModels | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.Paper.RingFamilyRestriction | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.NilpotentMarkedFreeComplexLift | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.NilpotentProjectiveComplexLift | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels | G3 | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.PseudoCoherentNilpotentInvariance | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed | Same signatures and projection values; no adaptation. |
| Sheaf.RingTheory.UnmarkedFiniteFreeLift | unclaimed | Same signatures and projection values; no adaptation. |

The repaired packet compiled both delivered modules and all seven external textual
projection users, plus the direct consumer `NormalizedRingHomExtension`, unchanged
and without warnings. The consumer checks took 2.5 to 36.7 seconds; the completed
differential module took 22.3 seconds without profiling. The upstream projection
import also passes the import-direction check.

## Status

landed 20261020T132035-L-1405424 2026-10-20 (merge of deliver/R3/Sheaf.Algebra.Homology.RingHomExtensionDifferential)
