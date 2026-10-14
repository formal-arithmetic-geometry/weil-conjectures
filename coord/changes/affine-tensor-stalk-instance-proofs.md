# AlgebraicGeometry.affineTensorPullbackHomologyStalkIso

## Reason

Repeatedly unfolding the sheaf comparison and converting its stalk isomorphism
through a linear equivalence makes the coordinate proof exceed 60 seconds.
Factor the existing sheaf comparison into the real, named definition
`affineTensorPullbackHomologySheafIso`, with explicit sheaf-module functors and their original category
instances. Its construction uses `Functor.mapHomologicalComplexCompIso`, implemented by
`NatIso.mapHomologicalComplex`, exactly as the original construction does. Add a direct module-isomorphism additive
equivalence and an affine localized-stalk equivalence, each with a proved
forward-map equation. The localized-stalk API composes those named constructions. The public coordinate
keeps the original `toLinearEquiv.toAddEquiv` projection directly, using the named
sheaf comparison rather than routing through both additive wrapper definitions.
The original coordinate signature and forward and inverse maps are unchanged.
The exact homology factors, tensor comparison, localization map and chosen
isomorphism are the original ones. There is no new choice of data or holed definition.

The new definition module is publicly imported because the public coordinate's
body uses it. The two theorem modules are imported only for the proof. The existing
public import and every existing signature and visibility stay unchanged.

## Old

```lean
def affineTensorPullbackHomologyStalkIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum A') (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex (.up ℤ)).obj P
    LocalizedModule p.asIdeal.primeCompl
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i) ≃+
        (RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
              (DerivedCategory.Q.obj T)) := by
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} A' ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) := tilde.functor (.of A')
  let : TA.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TA.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A'
  let f := Spec.map (CommRingCat.ofHom φ)
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let θ : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  let P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ :=
    (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C : CochainComplex (ModuleCat.{u} A') ℤ :=
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let T : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj P
  let δ : T ≅ (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk A' p).hom
  let t : C.homology i →ₗ[A'] (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    StructureSheaf.toStalkₗ A' (C.homology i) p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ A' (C.homology i) p))
  let l : LocalizedModule p.asIdeal.primeCompl (C.homology i) ≃ₗ[A']
      (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    IsLocalizedModule.iso p.asIdeal.primeCompl t
  let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj T) :=
    ((C.sc i).mapHomologyIso TB).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((TB.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫
      H.mapIso (DerivedCategory.Q.mapIso δ).symm
  exact l.toAddEquiv.trans (s.mapIso d).toLinearEquiv.toAddEquiv
```

## New

```lean
def affineTensorPullbackHomologyStalkIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum A') (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex (.up ℤ)).obj P
    LocalizedModule p.asIdeal.primeCompl
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i) ≃+
        (RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
              (DerivedCategory.Q.obj T)) := by
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
  let l := IsLocalizedModule.iso p.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ A' (C.homology i) p)
  -- Keep the original equivalence projections visible to definitional consumers.
  exact l.toAddEquiv.trans
    (s.mapIso (affineTensorPullbackHomologySheafIso A A' φ M i)).toLinearEquiv.toAddEquiv
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates | T4 | Same coordinate; proof reduced to one global-sections identity. |
| Sheaf.Algebra.Homology.AffineBaseChangeOrdinaryStalkComparison | unclaimed | Same coordinate and signature; no adaptation. |
| Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates | unclaimed | Same coordinate and signature; no adaptation. |

Users were enumerated with `tools/downstream.py --uses affineTensorPullbackHomologyStalkIso`.
No target statement changes. The underlying maps are identical; the named
sheaf comparison replaces their repeated inlining. The independent
statement review should verify this definitional refactoring, since the definition
is in the targets' dependency closure. No consumer is adapted by this delivery.

Repair H10: the returned artifacts reproduced the unchanged ordinary tensor-stalk
consumer's 60-second timeout. A profiling copy localized expensive definitional
normalization and kernel checks; the unchanged consumer's final `change` unfolds
the whole coordinate to its original three homology factors. The repaired
`affineTensorPullbackHomologySheafIso` uses explicitly typed `TA`, `TB` and `E`,
the original additive instances, and `Functor.mapHomologicalComplexCompIso`.
The redundant local `HasDerivedCategory` instance is removed. The public stalk
coordinate keeps the original localization/linear-equivalence projection visible,
instead of nesting the two new additive wrappers. No data, signature, consumer
source, timeout or file boundary changes.

After rebuilding the delivered dependencies, the original
`Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates` compiled against the
repaired explicit-instance construction in 58.8 seconds and against the final
flattened coordinate in 59.0 seconds, without errors or warnings. Both used the
standard 60-second launcher limit and the original repository source. The checks
ran after artifact regeneration finished. The latter is the final delivered
construction; the original consumer's final coordinate equality remains unchanged.
The other original direct importer,
`Sheaf.Algebra.Homology.AffineBaseChangeOrdinaryStalkComparison`, compiled against
the final artifacts in 29.7 seconds without errors or warnings. The existing item
definition and both theorem signatures are textually unchanged.


## Status

landed 20261014T043533-L-1336322 2026-10-14 (merge of deliver/T4/Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates)
