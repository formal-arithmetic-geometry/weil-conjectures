/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeGlobalComparison
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeStalkComparison

/-! # Affine base change computed on a module K-flat resolution

## References

* Stacks Project, Tag 0DJ8
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Compute the source model on a termwise tilde of a K-flat module complex. -/
theorem exists_affineBaseChangeTildeSourceModel
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ) :
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    ∃ (U : ModuleCat.{u} A') (a : U ⟶ V)
      (eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom φg))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf))).obj K))),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L ∧
      ∀ p : PrimeSpectrum A',
        let r := affineBaseChangeIntoPullback
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
          sq K ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) e hc p i
        ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk r).left,
          ∀ x, affineDerivedCohomologyStalkIso A' i p L
            (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = r (lU x) := by
  let : Algebra R A := φf.toAlgebra
  let : Algebra R R' := φg.toAlgebra
  have hs : IsPushout (CommRingCat.ofHom φf) (CommRingCat.ofHom φg)
      (CommRingCat.ofHom φg') (CommRingCat.ofHom φf') :=
    (IsPullback.of_map_of_faithful Scheme.Spec sq).unop.flip
  let ht := CommRingCat.isPushout_tensorProduct R A R'
  let τ := ht.isoIsPushout (CommRingCat.of A) (CommRingCat.of R') hs
  let : Algebra (TensorProduct R A R') A' := τ.hom.hom.toAlgebra
  have hφg' : (algebraMap (TensorProduct R A R') A').comp
      (algebraMap A (TensorProduct R A R')) = φg' := by
    exact congrArg CommRingCat.Hom.hom
      (IsPushout.inl_isoIsPushout_hom (CommRingCat.of A) (CommRingCat.of R') ht hs)
  have hφf' : (algebraMap (TensorProduct R A R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf' := by
    exact congrArg CommRingCat.Hom.hom
      (IsPushout.inr_isoIsPushout_hom (CommRingCat.of A) (CommRingCat.of R') ht hs)
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} R')
  let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
  obtain ⟨d, eU, ha⟩ := exists_affineBaseChangeTildeGlobalComparison
    R A R' A' φg' φf' hφg' hφf' sq K hK hL M hM e hc i m
  refine ⟨d, affineBaseChangeTildeModule R A R' A' M m i,
    affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i _
      (affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i), eU, ha, ?_⟩
  exact affineBaseChangeTildeModuleMap_localized
    R A R' A' φg' φf' hφg' hφf' sq K hK hL M hM e hc i m


end AlgebraicGeometry
