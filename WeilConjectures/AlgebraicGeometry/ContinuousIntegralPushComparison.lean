/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationHomology
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationMate
/-! # Integral localization commutes with bounded qcqs derived pushforward -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The unit of `LY ⊣ UY` followed by the pushed mate of a comparison `κ : H ⋙ UY ≅ UX ⋙ G` is
`G` applied to the unit of `LX ⊣ UX`. -/
theorem mate_unit_comap
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY) {G : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ UY ≅ UX ⋙ G) (K : A) :
    adjY.unit.app (G.obj K) ≫
        (UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) ≫
          κ.hom.app (LX.obj K)) = G.map (adjX.unit.app K) := by
  have h := unit_mateEquiv_symm adjX adjY (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adjX.unit.app K) ≫ κ.inv.app (LX.obj K) =
    adjY.unit.app (G.obj K) ≫
      UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) at h
  have hh := congrArg (fun z ↦ z ≫ κ.hom.app (LX.obj K)) h.symm
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  exact hh.trans (Category.comp_id (G.map (adjX.unit.app K)))

/-- The zeroth legs of the localization-unit cocones of `adjY` at `G K` and of `G` applied to
that of `adjX` at `K` agree after a comparison `g` that is compatible with the units. -/
theorem localization_comparison_zero (ℓ : ℕ)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    [UX.Additive] [UY.Additive] (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    (G : A ⥤ C) [G.Additive] (K : A)
    [IsIso (ℓ • 𝟙 (LX.obj K))] [IsIso (ℓ • 𝟙 (LY.obj (G.obj K)))]
    (g : UY.obj (LY.obj (G.obj K)) ⟶ G.obj (UX.obj (LX.obj K)))
    (hg : adjY.unit.app (G.obj K) ≫ g = G.map (adjX.unit.app K)) :
    (scalarLocalizationUnitCocone ℓ adjY (G.obj K)).ι.app 0 ≫ g =
      ((Cocone.precompose (Mod.smulSequenceCompIso G K ℓ).inv).obj
        (G.mapCocone (scalarLocalizationUnitCocone ℓ adjX K))).ι.app 0 := by
  simp only [scalarLocalizationUnitCocone, Functor.comp_obj, Functor.const_obj_obj, pow_zero,
    End.one_asHom, CategoryTheory.Functor.map_id, Category.comp_id, Mod.smulSequenceCompIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app]
  change adjY.unit.app (G.obj K) ≫ g = 𝟙 _ ≫ G.map (adjX.unit.app K)
  exact hg.trans (Category.id_comp (G.map (adjX.unit.app K))).symm

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

set_option maxHeartbeats 400000 in
-- The cocone comparisons below unify large derived module categories.
/-- The specified scalar-extension/pushforward mate is invertible on integral bounded
constructible complexes for a qcqs map.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-integral-push-comparison).

Proof in words. Express the restricted regular E coefficient module as the sequential
colimit O --ℓ--> O --ℓ--> ..., with nth map a ↦ a/ℓⁿ. The compact-test localization
calculation and exact monoidal inverse image identify this colimit on every scheme.
Tensoring a complex with this coefficient module is therefore its localization telescope.
Exactness of filtered colimits and integralScalarExtension_exact identify derived scalar
extension with this termwise operation. Choose a good truncation of a representative of K
below its lower cohomological bound. Every term of its telescope has this same lower bound.
Apply condensed_qcqs_pushforward_continuity in every cohomological degree. It makes the
natural map from the telescope of Rf_*K to Rf_* of the telescope an isomorphism in every
degree. The map so obtained is the specified derivedPushHom: both are adjoint to the
restriction-of-scalars/pushforward comparison, and on the nth localization leg they are
induced by the same unit and division by ℓⁿ. Homology detects isomorphisms in the derived
category, and the exact faithful restriction functor reflects isomorphisms. No proper base
change theorem or completed pushforward is used. The zero complex and empty schemes give
the same zero-object comparison. -/
theorem integralScalarPushHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (K : integralConstructible ℓ E X) :
    IsIso ((derivedPushHom (integralScalarMap ℓ E) f).app K.obj) := by
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let a := integralScalarMap ℓ E
  let G := (lowerStar (integralCoeff ℓ E) f).rightDerivedFunctor
  let U := (Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap a Y)).mapDerivedCategory
  let UX := (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap a X)).mapDerivedCategory
  let LX := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let κ := derivedComapLowerStarIso a f
  let β : (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj (G.obj K.obj) ⟶
      (lowerStar (Profinite.continuousMapRingObj E) f).rightDerivedFunctor.obj
        (LX.obj K.obj) := (derivedPushHom a f).app K.obj
  have : G.IsRightAdjoint :=
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f).isRightAdjoint
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : G.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hK : DerivedCategory.TStructure.t.plus K.obj := K.property.1.1
  have hGK : DerivedCategory.TStructure.t.plus (G.obj K.obj) := by
    obtain ⟨n, hn⟩ := hK
    have : K.obj.IsGE n := hn
    let K' : DerivedCategory.Plus _ := ⟨K.obj, ⟨n, hn⟩⟩
    have : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 hn
    refine ⟨n, (DerivedCategory.isGE_iff _ n).2 fun q hq ↦ ?_⟩
    exact (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar (integralCoeff ℓ E) f) K' n hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso
          ((lowerStar (integralCoeff ℓ E) f).rightDerivedFunctorPlusCompatibility.app K')).symm
  let cX := integralLocalizationCocone ℓ E X K.obj
  let cY := integralLocalizationCocone ℓ E Y (G.obj K.obj)
  let σ := Mod.smulSequenceCompIso G K.obj ℓ
  let d := (Cocone.precompose σ.inv).obj (G.mapCocone cX)
  let g : cY.pt ⟶ d.pt := U.map β ≫ κ.hom.app (LX.obj K.obj)
  have : IsIso (ℓ • 𝟙 d.pt) := by
    have := derived_nsmul_isIso ℓ E X (LX.obj K.obj)
    have h : IsIso (G.map (UX.map (ℓ • 𝟙 (LX.obj K.obj)))) := inferInstance
    change IsIso (ℓ • 𝟙 (G.obj (UX.obj (LX.obj K.obj))))
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  have := derived_nsmul_isIso ℓ E X (LX.obj K.obj)
  have := derived_nsmul_isIso ℓ E Y
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj (G.obj K.obj))
  have hzero : cY.ι.app 0 ≫ g = d.ι.app 0 := by
    exact localization_comparison_zero ℓ adjX adjY G K.obj g
      (mate_unit_comap adjX adjY κ K.obj)
  have hU : U.ReflectsIsomorphisms := by
    let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (coefficientMap a Y)
    have : V.ReflectsIsomorphisms := by
      refine ⟨fun {M N} z hz ↦ ?_⟩
      have : IsIso z.hom := by
        change IsIso ((Mod.forget _).map (V.map z))
        infer_instance
      have : IsIso ((Mod.forget _).map z) := by
        change IsIso z.hom
        infer_instance
      exact isIso_of_reflects_iso z (Mod.forget _)
    refine ⟨fun z _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro q
    have : IsIso (V.map ((DerivedCategory.homologyFunctor _ q).map z)) :=
      (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso q) z).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ V
  have : IsIso (U.map β) := by
    have hgg : IsIso g := by
      rw [DerivedCategory.isIso_iff]
      intro q
      let H := DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) Y)) q
      obtain ⟨hc⟩ := integralLocalization_homology_isColimit ℓ E Y (G.obj K.obj) hGK q
      obtain ⟨hd⟩ := integralLocalization_push_homology_isColimit ℓ E f K.obj hK q
      apply integralLocalization_cocone_map_isIso ℓ cY d g hzero H hc
      let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
      let e := Functor.isoWhiskerRight (Functor.isoWhiskerLeft J σ) H
      refine (IsColimit.precomposeHomEquiv e _) ?_
      apply hd.ofIsoColimit
      exact Cocone.ext (Iso.refl _) (by
        intro n
        simp only [Functor.comp_obj, Mod.smulSequenceCompIso, NatIso.ofComponents_hom_app,
          Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
          Cocone.precompose_obj_pt, Functor.mapCocone_pt, Cocone.whisker_pt,
          Functor.mapCocone_ι_app, Functor.comp_map, Iso.refl_hom, Category.comp_id,
          Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.const_obj_obj,
          Functor.whiskerRight_app, Functor.whiskerLeft_app,
          CategoryTheory.Functor.map_id, Cocone.whisker_ι, Functor.whiskerLeft_comp,
          Functor.map_comp, e, σ, d]
        change H.map (G.map (cX.ι.app n.down)) =
          𝟙 _ ≫ H.map (𝟙 _) ≫ H.map (G.map (cX.ι.app n.down))
        rw [H.map_id, Category.id_comp, Category.id_comp])
    have : U.map β = g ≫ κ.inv.app (LX.obj K.obj) := by
      simp only [g, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id (U.map β)).symm
    rw [this]
    infer_instance
  exact isIso_of_reflects_iso β U

end

end AlgebraicGeometry.ProEtale.CondensedRing

