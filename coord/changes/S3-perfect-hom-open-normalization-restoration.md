# AlgebraicGeometry.perfectHomOpenDerivedComparison

## Reason

Restore the quarantined stage-3 rework item
`Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization`.
Its archive has zero holes but uses the withdrawn Sheaf transport module,
the retired `restriction_additive` helper, and the obsolete exact-composition
comparison lemma name. Merely restoring that source fails to elaborate.

The adopted source module already constructs both comparison isomorphisms and
proves the identical normalization theorem. Restore the Sheaf path as a public
compatibility import, following the existing AffineGlobalHomBaseChangeMap wrapper.
The source's declarations and proofs are untouched. The node retains its exact
statement, declaration names, statement dependencies, proof and proof dependencies;
its Lean attachment now identifies the adopted source declarations directly.
The quarantine archive is preserved, and no path is listed in deleted.txt.

## Old

The two archived public constructions, verbatim:

```lean
def perfectHomOpenDerivedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) := by
  let : HasDerivedCategory.{w} (pullback s r).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)))
  let : HasDerivedCategory.{w} (pullback (B.ι ≫ s) r).Modules := inferInstanceAs
    (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback (B.ι ≫ s) r).toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{w} B.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace)))
  have : IsGrothendieckAbelian.{u} (pullback s r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (pullback (B.ι ≫ s) r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} Y.Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : Abelian.HasKInjectiveResolutions (pullback s r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions (pullback (B.ι ≫ s) r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions Y.Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let F := Scheme.Modules.pushforward (pullback.fst s r)
  let G := schemeOpenRestriction Y B
  let H := Scheme.Modules.restrictFunctor (perfectHomOpenMap s B r)
  let K := Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r)
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits H :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).1
  have : H.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).2
  have : F.Additive := inferInstance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := restriction_additive _
  have : K.Additive := inferInstance
  have : (F ⋙ G).Additive := inferInstance
  have : (H ⋙ K).Additive := inferInstance
  have : IsIso (perfectHomOpenModuleMate s B r) := perfectHomOpenModuleMate_isIso s B r
  let aH : H.mapDerivedCategory ⊣ schemeDerivedDirectImage (perfectHomOpenMap s B r) :=
    (Scheme.Modules.restrictAdjunction (perfectHomOpenMap s B r))
      |>.mapDerivedCategoryRightDerivedAdjunction
  let σH : H.mapDerivedCategory ≅ derivedPullback (perfectHomOpenMap s B r) :=
    (conjugateIsoEquiv (canonicalPullbackAdjunction (perfectHomOpenMap s B r)) aH).symm
      (Iso.refl _)
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w} F G).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w}
      (asIso (perfectHomOpenModuleMate s B r)) ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1, w, w, w} H K ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} H) _
      ≪≫ Functor.isoWhiskerRight σH _

/-- Transport the explicitly derived comparison to the supplied adjunctions.
The conjugations are isomorphisms determined by the identity of the left adjoints.
Source: Stacks Tag 079W and Mathlib's adjoint uniqueness
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenSuppliedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (ap : derivedPullback (pullback.fst s r) ⊣
      schemeDerivedDirectImage (pullback.fst s r))
    (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
      schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) :=
  let σ := (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let σ₀ := (conjugateIsoEquiv (canonicalPullbackAdjunction B.ι)
    (schemeMVAdjunction Y B)).symm (Iso.refl _)
  Functor.isoWhiskerRight
      ((conjugateIsoEquiv ap (canonicalPullbackAdjunction (pullback.fst s r)))
        (Iso.refl _)) (schemeMVDerivedRestriction Y B) ≪≫
    Functor.isoWhiskerLeft (schemeDerivedDirectImage (pullback.fst s r)) (σ ≪≫ σ₀.symm) ≪≫
    perfectHomOpenDerivedComparison s B r ≪≫
    Functor.isoWhiskerLeft (derivedPullback (perfectHomOpenMap s B r))
      ((conjugateIsoEquiv (canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)) ap')
        (Iso.refl _))

```

The archived normalization signature, verbatim:

```lean
theorem perfectHomOpenComparison_counit_resolution
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let a := canonicalPullbackAdjunction B.ι
    let ap := canonicalPullbackAdjunction (pullback.fst s r)
    let ap' := canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)
    let b := perfectHomOpenMap s B r
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, perfectHomOpenMap, pullback.map]
    let κ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
        ((perfectHomOpenDerivedComparison s B r).hom.app
          (DerivedCategory.Q.obj I)) ≫
        ap'.counit.app ((derivedPullback b).obj (DerivedCategory.Q.obj I)) =
      κ.inv.app ((schemeDerivedDirectImage (pullback.fst s r)).obj
        (DerivedCategory.Q.obj I)) ≫
        (derivedPullback b).map (ap.counit.app (DerivedCategory.Q.obj I))
```

## New

The restored module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization

/-! # Normalization of the open-square comparison on K-injective representatives

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.perfectHomOpenComparison_counit_resolution` and its two explicit
comparison constructions. Re-exporting the source declarations restores the quarantined
interface using the current exact-composition comparison and open-restriction instances.

Source: Stacks Project, Cohomology, Tags 08FE, 08BS, 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization).
-/

@[expose] public section
```

The adopted constructions exposed by that import, verbatim:

```lean
def perfectHomOpenDerivedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) := by
  let : HasDerivedCategory.{w} (pullback s r).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)))
  let : HasDerivedCategory.{w} (pullback (B.ι ≫ s) r).Modules := inferInstanceAs
    (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback (B.ι ≫ s) r).toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{w} B.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace)))
  have : IsGrothendieckAbelian.{u} (pullback s r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (pullback (B.ι ≫ s) r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} Y.Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : Abelian.HasKInjectiveResolutions (pullback s r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions (pullback (B.ι ≫ s) r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions Y.Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let F := Scheme.Modules.pushforward (pullback.fst s r)
  let G := schemeOpenRestriction Y B
  let H := Scheme.Modules.restrictFunctor (perfectHomOpenMap s B r)
  let K := Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r)
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits H :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).1
  have : H.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).2
  have : F.Additive := inferInstance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := inferInstance
  have : K.Additive := inferInstance
  have : (F ⋙ G).Additive := inferInstance
  have : (H ⋙ K).Additive := inferInstance
  have : IsIso (perfectHomOpenModuleMate s B r) := perfectHomOpenModuleMate_isIso s B r
  let aH : H.mapDerivedCategory ⊣ schemeDerivedDirectImage (perfectHomOpenMap s B r) :=
    (Scheme.Modules.restrictAdjunction (perfectHomOpenMap s B r))
      |>.mapDerivedCategoryRightDerivedAdjunction
  let σH : H.mapDerivedCategory ≅ derivedPullback (perfectHomOpenMap s B r) :=
    (conjugateIsoEquiv (canonicalPullbackAdjunction (perfectHomOpenMap s B r)) aH).symm
      (Iso.refl _)
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w} F G).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w}
      (asIso (perfectHomOpenModuleMate s B r)) ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1, w, w, w} H K ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} H) _
      ≪≫ Functor.isoWhiskerRight σH _

/-- Transport the explicitly derived comparison to the supplied adjunctions.
The conjugations are isomorphisms determined by the identity of the left adjoints.
Source: Stacks Tag 079W and Mathlib's adjoint uniqueness
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenSuppliedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (ap : derivedPullback (pullback.fst s r) ⊣
      schemeDerivedDirectImage (pullback.fst s r))
    (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
      schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) :=
  let σ := (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let σ₀ := (conjugateIsoEquiv (canonicalPullbackAdjunction B.ι)
    (schemeMVAdjunction Y B)).symm (Iso.refl _)
  Functor.isoWhiskerRight
      ((conjugateIsoEquiv ap (canonicalPullbackAdjunction (pullback.fst s r)))
        (Iso.refl _)) (schemeMVDerivedRestriction Y B) ≪≫
    Functor.isoWhiskerLeft (schemeDerivedDirectImage (pullback.fst s r)) (σ ≪≫ σ₀.symm) ≪≫
    perfectHomOpenDerivedComparison s B r ≪≫
    Functor.isoWhiskerLeft (derivedPullback (perfectHomOpenMap s B r))
      ((conjugateIsoEquiv (canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)) ap')
        (Iso.refl _))

```

The normalization theorem has the exact archived signature displayed above.
Compatibility is checked by reproducing the archived constructions with the
current additive instance and proving their equality to the adopted constructions
by reflexivity, and by applying the adopted theorem to the full archived signature.
These compatibility checks compile in 9.5 seconds. Both comparisons and the
theorem have only propext, Classical.choice and Quot.sound as axioms (separate
compiled probe, 1.8 seconds). A scratch copy of the direct consumer compiles
through the restored Sheaf import in 5.6 seconds after compiling the wrapper
in 1.9 seconds. No additional hypothesis, universe restriction or changed
canonical choice is used.
The empty/full-open and zero-complex cases retain the same constructions.

## Users

There are no current Lean importers of the absent Sheaf path, including in quarantine.
The DAG parent `lem-pc-perfect-hom-open-comparison-mate-is-iso` is preserved: it is
already attached to the source consumer `PerfectHomOpenComparisonMateIso`, which
imports the adopted normalization module. Thus this is restoration of the same
public interface, not a claim that zero importers authorize withdrawal.

Source-only `tools/downstream.py` on the adopted module gives the following
transitive consumers. Its three public names are mentioned only in that module
itself and its direct consumer `PerfectHomOpenComparisonMateIso`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_three | unclaimed | Existing source interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_zero | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectDescendMorphisms | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisColumns | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEvenThree | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEvenZero | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenComparisonMateIso | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedData | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedEquiv | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomOpenTestBijective | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomPresentation | unclaimed | Existing source interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.RecordedPerfectHomContinuity | unclaimed | Existing source interface unchanged; no adaptation. |

The restored item is held by S3. No other module is edited, no definition or
statement changes meaning, no target review is reopened, and the unit
`sk-thm-picard-semicon` retains its statement and realized proof step.

## Status

landed 20261021T225218-L-3797398 2026-10-21 (merge of deliver/S3/Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization)
