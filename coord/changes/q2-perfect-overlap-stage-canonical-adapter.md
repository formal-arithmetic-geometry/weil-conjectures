# AlgebraicGeometry.overlapOpenInclusionPullbackIso

## Reason

Rework entry 260 quarantined this module after an import collision between the Sheaf and
adopted-source definitions of `derivedPullback`. The adopted source now supplies all six
constructed overlap definitions. Restore this module as a public adapter to that source,
without a second declaration of any source name. Reprove the four archived helper theorems
for the source constructions. The inclusion comparison below changes construction route:
its old descent witness is replaced by the source's explicit adjunction and left-derived
uniqueness construction. The stage-object association change is recorded separately in
`q2-perfect-overlap-stage-object-normalization.md`. Its type and all four helper signatures
are preserved. No target statement or adopted-source file is edited.

## Old

The archived definition, verbatim:

```lean
@[no_expose] noncomputable def overlapOpenInclusionPullbackIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    derivedPullback (X.homOfLE (leOfHom i)) ≅
      (schemeOpenOverlapRestriction X i).mapDerivedCategory := by
  classical
  let R := (schemeOpenRestriction X U).mapDerivedCategory
  let h := X.homOfLE (leOfHom i)
  let α : R ⋙ derivedPullback h ≅
      R ⋙ (schemeOpenOverlapRestriction X i).mapDerivedCategory :=
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso X U).symm
        (derivedPullback h) ≪≫
      perfectHomComposition h U.ι ≪≫
        eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
          (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i))) ≪≫
          singleComplexOpenPullbackIso X W ≪≫
            (schemeDerivedOpenRestrictionCompIso X i).symm
  exact Classical.choose (Scheme.derived_open_restriction_iso_descent X U
    (derivedPullback h) (schemeOpenOverlapRestriction X i).mapDerivedCategory α)
```

## New

The module publicly imports
`WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence`. That unchanged source
supplies the following definition, verbatim; the adapter does not redeclare it:

```lean
noncomputable def overlapOpenInclusionPullbackIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    derivedPullback (X.homOfLE (leOfHom i)) ≅
      (schemeOpenOverlapRestriction X i).mapDerivedCategory := by
  classical
  let f := X.homOfLE (leOfHom i)
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let Q := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)
  have : (derivedPullback f).IsLeftDerivedFunctor ε Q :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  let η : T ≅ Scheme.Modules.restrictFunctor f :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let restriction : schemeOpenOverlapRestriction X i ≅ Scheme.Modules.restrictFunctor f :=
    Functor.isoWhiskerLeft (Scheme.Modules.overEquiv U).inverse
        (Scheme.Modules.overMapCompOverEquiv i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).counitIso _ ≪≫ Functor.leftUnitor _
  let θ : schemeOpenOverlapRestriction X i ≅ T := restriction ≪≫ η.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom Q :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback f) ε
    T.mapDerivedCategoryFactorsh.hom Q ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm
```

The other five archived definitions are likewise supplied by that public import. Four
have the same bodies modulo whitespace. The canonical stage-object comparison associates
the fixed composition maps differently; its normalization is proved by the retained
`perfectOverlapStageObjectIso_hom_app` theorem and recorded separately. Every adopted-source
signature and body remains unchanged. The adapter retains all four archived helper
signatures and proves their bodies for these canonical definitions. The pin equation is
proved from restriction-adjunction coherence and the pinned derived counit triangle,
so the compatibility previously obtained from descent is recovered as a theorem.

## Users

The current `tools/downstream.py --allow-missing --uses` query has no active Lean users:
the item and its consumers are quarantined. This is not treated as withdrawal authority.
The direct quarantined importers and the indirect user of the restored helper were read;
none unfolds the old descent construction. Their node attachments and dependency links
remain intact. All use the same exported types and helper equations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization` | unclaimed | Uses the restored hom-component equation through the nested-square interface; signature preserved. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent` | unclaimed | Uses the restored stage-object component equation; signature preserved. |

No consumer is adapted. No source-library declaration, signature, attribute, public import,
or data body is changed. Targets that use these definitions retain the adopted source
construction; the restored adapter and its compatibility proof are available for semantic
review together with this change record.

## Status

landed 20261020T230822-L-616945 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence)
