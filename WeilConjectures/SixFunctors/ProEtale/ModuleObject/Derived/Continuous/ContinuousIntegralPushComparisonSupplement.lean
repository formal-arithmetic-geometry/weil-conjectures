/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationHomology
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison

/-! # Integral localization commutes with bounded qcqs derived pushforward -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

set_option maxHeartbeats 800000 in
-- The proof instantiates the two geometric derived adjunctions and their homology comparisons.
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
  -- Upstream's localization cocones live over `Mod.smulSequence`; precompose them with the
  -- identity-component comparison from `integralLocalizationSequence`.
  let ιX : integralLocalizationSequence ℓ K.obj ⟶ Mod.smulSequence K.obj ℓ :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [integralLocalizationSequence, Functor.ofSequence_map_homOfLE_succ,
        Nat.add_sub_cancel_left, pow_one]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let ιY : integralLocalizationSequence ℓ (G.obj K.obj) ⟶ Mod.smulSequence (G.obj K.obj) ℓ :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [integralLocalizationSequence, Functor.ofSequence_map_homOfLE_succ,
        Nat.add_sub_cancel_left, pow_one]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let cX := (Cocone.precompose ιX).obj (integralLocalizationCocone ℓ E X K.obj)
  let cY := (Cocone.precompose ιY).obj (integralLocalizationCocone ℓ E Y (G.obj K.obj))
  let σ := integralLocalizationSequenceMapIso ℓ G K.obj
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
    have h := localization_comparison_zero ℓ adjX adjY G K.obj g
      (mate_unit_comap adjX adjY κ K.obj)
    simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app,
      Mod.smulSequenceCompIso, NatIso.ofComponents_inv_app, Iso.refl_inv] at h
    simp only [cY, d, cX, σ, ιX, ιY, Cocone.precompose_obj_ι, NatTrans.comp_app,
      Functor.mapCocone_ι_app, NatTrans.ofSequence_app, Category.id_comp,
      integralLocalizationSequenceMapIso, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_id]
    exact h
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
        simp only [Functor.comp_obj, integralLocalizationSequenceMapIso,
          Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, asIso_hom, asIso_inv,
          Cocone.precompose_obj_pt, Functor.mapCocone_pt, Cocone.whisker_pt,
          Functor.mapCocone_ι_app, Functor.comp_map, Iso.refl_hom, Category.comp_id,
          Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.const_obj_obj,
          Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.ofSequence_app,
          CategoryTheory.Functor.map_id, Cocone.whisker_ι, Functor.whiskerLeft_comp,
          NatIso.isIso_inv_app, IsIso.inv_id, Functor.map_comp, e, σ, d]
        change H.map (G.map (cX.ι.app n.down)) =
          𝟙 _ ≫ H.map (𝟙 _) ≫ H.map (G.map (cX.ι.app n.down))
        rw [H.map_id, Category.id_comp, Category.id_comp])
    have : U.map β = g ≫ κ.inv.app (LX.obj K.obj) := by
      simp only [g, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id (U.map β)).symm
    rw [this]
    infer_instance
  exact isIso_of_reflects_iso β U

end AlgebraicGeometry.ProEtale.CondensedRing
