/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeSourceModel
import WeilConjectures.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso
import WeilConjectures.Algebra.Homology.RingTensorCohomology
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import all WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore

/-! # Source model for the affine derived base-change arrow

The source model of the affine derived base-change arrow: a cohomology module with a map to the
canonical module of pullback cohomology.

## References

* Stacks Project, Tag 0DJ8 (affine proof)
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

/-- The affine base-change arrow has a cohomology module source and a map to the
canonical module of pullback cohomology. No target K', map phi or target coordinates
are involved. -/
theorem exists_affineBaseChangeSourceModel
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (i : ℤ) :
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
          sq K P e hc p i
        ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk r).left,
          ∀ x, affineDerivedCohomologyStalkIso A' i p L
            (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = r (lU x) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let ι := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let Kq : schemeDerivedQCohCategory (Spec (.of A)) := ⟨K, hK⟩
  obtain ⟨E, ⟨α⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core A
  let N := DerivedCategory.Q.objPreimage (E.inverse.obj Kq)
  let M := (RingTensorCohomology.resolution A).obj N
  let sM : M ⟶ N := (RingTensorCohomology.augmentation A).app N
  have hsM : QuasiIso sM := by
    dsimp [sM, RingTensorCohomology.augmentation]
    infer_instance
  have hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M :=
    (RingTensorCohomology.flatResolution A).kFlat_resolutionFunctor_obj
      ObjectProperty.flat.essImage_ι_le N
  have : IsIso (DerivedCategory.Q.map sM) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hsM
  let P₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ := T.obj M
  let e₀ : DerivedCategory.Q.obj P₀ ≅ K :=
    (α.app M).symm ≪≫ ι.mapIso
      (E.functor.mapIso
        (asIso (DerivedCategory.Q.map sM) ≪≫
          DerivedCategory.Q.objObjPreimageIso (E.inverse.obj Kq)) ≪≫ E.counitIso.app Kq)
  have hP₀ : CochainComplex.IsKFlatTensor (R := (Spec (.of A)).sheaf) P₀ :=
    isKFlat_tilde A M (by
      intro F hF
      have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
        ((HomotopyCategory.quotient _ (.up ℤ)).obj M)).mp
          ((HomotopyCategory.kFlat_quotient_obj_iff M).mpr hM)
      have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
        (h _ hF').2)
  have hc₀ : IsIso ((SingleComplexBaseChange.counit
      (Spec.map (CommRingCat.ofHom φg'))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P₀)) :=
    SingleComplexBaseChange.counit_isIso_of_isKFlat _ P₀ hP₀
  obtain ⟨d, U, a, eU, ha, hl⟩ := exists_affineBaseChangeTildeSourceModel
    R A R' A' φf φg φg' φf' sq K hK hL M hM e₀ hc₀ i
  refine ⟨d, U, a, eU, ha, ?_⟩
  intro p
  obtain ⟨l₀, hl₀⟩ := hl p
  obtain ⟨t, ht⟩ := exists_affineBaseChangeIntoPullback_representativeIso
    (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
    (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
    sq K P P₀ hP hP₀ e e₀ hc hc₀ p i
  refine ⟨l₀.trans t, ?_⟩
  intro x
  exact (hl₀ x).trans (ht (l₀ x))

end AlgebraicGeometry
