/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients

import WeilConjectures.CategoryTheory.Sites.MonObj
import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Scalar units in the integral coefficient sheaf

Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(blueprint: lem-weil-pbc-integral-scalar-contractive)

The continuous-ring realization argument is generalized from the proved comparison in
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` to a totally disconnected
continuous coefficient ring in Type 0. The helpers below also prove regular-module
linearity on sections and the norm-one continuous reciprocal formula.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj



namespace AlgebraicGeometry.ProEtale

private noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] : Profinite.continuousMapRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousMapRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private noncomputable def comparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

private lemma comparison_eq (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    (S : Profinite.{u}) (f : C(S, E)) :
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _
        (comparison X E)).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := by
  rw [comparison, Equiv.apply_symm_apply]
  rfl

private noncomputable def comparisonAdjointRing (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    Profinite.continuousMapRingSheaf E ⟶
      (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj
            (continuousMapRingSheaf X E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ContinuousMap.compRightAlgHom ℤ E (profiniteTestProjection X S.unop)).toRingHom).comp
            ULift.ringEquiv.toRingHom))
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩


private lemma comparisonAdjoint_isMonHom (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (comparisonAdjoint X E) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology specZ.{u}
  let L := Scheme.ProEt.topology X
  let R := continuousMapRingSheaf X E
  have h₁ := pushforwardRingMonObj F K L R
  have h₂ := pushforwardRingMonObj profiniteToProEt J K
    ((F.sheafPushforwardContinuous RingCat.{u + 1} K L).obj R)
  change @IsMonHom _ _ _ _ _ _
    ((profiniteToProEt.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).monObjObj
      (((F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K L).obj
        ((sheafCompose L (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R)))) _
  erw [← h₁, ← h₂]
  exact Sheaf.isMonHom_sheafCompose_map J (comparisonAdjointRing X E)

private lemma comparison_isMonHom (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (comparison X E) := by
  have := comparisonAdjoint_isMonHom X E
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let f : Mon.mk (Profinite.continuousMapRingObj E) ⟶
      ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)) ⋙ pointLowerStar).mapMon.obj
        (Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E))) := Mon.ofHom (comparisonAdjoint X E)
  let g := (a.mapMon.homEquiv _ _).symm f
  change IsMonHom g.hom
  exact g.isMonHom_hom

private noncomputable def kanComparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lan.obj (Profinite.continuousMapRingObj E).obj ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)).obj :=
  (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (comparisonAdjoint X E).hom

private lemma kanComparison_unit (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lanUnit.app (Profinite.continuousMapRingObj E).obj ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op (kanComparison X E) =
        (comparisonAdjoint X E).hom := by
  have h := (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv
    (Profinite.continuousMapRingObj E).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousMapRingSheaf X E)).obj).apply_symm_apply (comparisonAdjoint X E).hom
  dsimp only [kanComparison]
  rw [← Functor.lanAdjunction_unit]
  exact h

private lemma kanComparison_isIso (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (η : (Profinite.continuousMapRingObj E).obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (σ : P ⟶ ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousMapRingSheaf X E)).obj)
    (hp : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (hσ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op σ =
      (comparisonAdjoint X E).hom) : IsIso (σ.app (Opposite.op U)) := by
  let T := Profinite.of (ConnectedComponents U.left)
  let q := canonicalComponentArrow X U
  let a := η.app (Opposite.op T) ≫ P.map q.op
  have hi' := (hp (Opposite.op U)).isIso_ι_app_of_isTerminal
    (CostructuredArrow.mk (S := (profiniteToProEtOf X).op) q.op)
    (canonicalComponentArrow_terminal X U)
  have hi : IsIso a := hi'
  let Q := ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousMapRingSheaf X E)).obj
  have h : a ≫ σ.app (Opposite.op U) =
      (comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op := by
    dsimp only [a]
    rw [Category.assoc, σ.naturality]
    exact congrArg (fun f ↦ f ≫ Q.map q.op)
      (congr_app hσ (Opposite.op T))
  have hq (x : U.left) : profiniteTestProjection X T (q.left x) = ConnectedComponents.mk x := by
    have h := congrFun (congrArg DFunLike.coe
      ((pointComponentsEquiv X U T).apply_symm_apply (ContinuousMap.id _)))
      (ConnectedComponents.mk x)
    rw [pointComponentsEquiv_apply] at h
    exact h
  have hbij : Function.Bijective
      ((comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op) := by
    constructor
    · intro f g he
      apply ULift.ext
      ext t
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
      have h := congrArg (fun f ↦ f.down x) he
      change f.down (profiniteTestProjection X T (q.left x)) =
        g.down (profiniteTestProjection X T (q.left x)) at h
      simpa only [hq] using h
    · intro f
      refine ⟨ULift.up ⟨f.down.continuous.connectedComponentsLift,
        f.down.continuous.connectedComponentsLift_continuous⟩, ?_⟩
      apply ULift.ext
      ext x
      change f.down.continuous.connectedComponentsLift
        (profiniteTestProjection X T (q.left x)) = f.down x
      rw [hq, Continuous.connectedComponentsLift_apply_coe]
  have : IsIso (a ≫ σ.app (Opposite.op U)) := by
    rw [h]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsIso.of_isIso_comp_left a _

private lemma comparison_basis_isIso (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U) :
    IsIso ((comparison X E).hom.app (Opposite.op U)) := by
  let F := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let Λ := Profinite.continuousMapRingObj E
  let H := (sheafCompose K (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (continuousMapRingSheaf X E)
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).IsContinuous
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have : F.IsContinuous J K := by
    exact Functor.isContinuous_comp profiniteToProEt
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) J
      (Scheme.ProEt.topology specZ) K
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    AddCommGrpCat.{u + 1} J K
  let e := Adjunction.leftAdjointUniq a b
  let f := (b.homEquiv Λ H).symm (comparisonAdjoint X E)
  have hcomp : comparison X E = e.hom.app Λ ≫ f := by
    apply (a.homEquiv Λ H).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [comparison, Equiv.apply_symm_apply]
    change comparisonAdjoint X E = (b.homEquiv Λ H) f
    exact ((b.homEquiv Λ H).apply_symm_apply (comparisonAdjoint X E)).symm
  let P := F.op.lan.obj Λ.obj
  let η := F.op.lanUnit.app Λ.obj
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension P η
  have hu := (proEtale_sheafification_wcontractible_sections X).2.1 Λ P η hp U
    inferInstance wU
  have : IsIso ((toSheafify K P).app (Opposite.op U)) := hu.1
  have hunit : (toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U) =
      (kanComparison X E).app (Opposite.op U) := by
    change (((sheafificationAdjunction K AddCommGrpCat.{u + 1}).homEquiv P H)
      f).app (Opposite.op U) = _
    simp only [ObjectProperty.ι_obj,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.restrictFullyFaithful, Functor.id_obj, Functor.comp_obj,
      Functor.whiskeringLeft_obj_obj, Functor.FullyFaithful.homEquiv,
      Functor.FullyFaithful.id, Iso.refl_symm, Equiv.trans_def, Adjunction.comp_homEquiv,
      Equiv.symm_mk, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_trans,
      Iso.homCongr_symm, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
      Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Iso.app_inv, NatTrans.id_app,
      Category.id_comp, Iso.symm_inv, Iso.app_hom, Iso.refl_hom, Category.comp_id,
      kanComparison, f, b]
    erw [Category.id_comp, Category.comp_id, Equiv.apply_symm_apply]
  have : IsIso ((kanComparison X E).app (Opposite.op U)) :=
    kanComparison_isIso X E U P η (kanComparison X E) hp (kanComparison_unit X E)
  have : IsIso (f.hom.app (Opposite.op U)) := by
    have : IsIso ((toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U)) := by
      rw [hunit]
      infer_instance
    exact IsIso.of_isIso_comp_left ((toSheafify K P).app (Opposite.op U)) _
  rw [hcomp]
  change IsIso ((e.hom.app Λ).hom.app (Opposite.op U) ≫ f.hom.app (Opposite.op U))
  infer_instance


private theorem integralComparison_isIso (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    IsIso (comparison X T) :=
  isIso_of_affine_weaklyContractible X (comparison X T) (fun U hU wU ↦ by
    let _ := hU
    exact comparison_basis_isIso X T U wU)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open MonObj
private lemma continuousRegular_map_mul (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    (f : Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)) ⟶
      Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)))
    (U : X.ProEtᵒᵖ) (a b : ULift.{u + 1} C(U.unop.left, T)) :
    f.hom.hom.app U (a * b) =
      a * (show ULift.{u + 1} C(U.unop.left, T) from f.hom.hom.app U b) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let : MonObj R.obj := (continuousMapRingSheaf X T).obj.monObjCompForget₂
  let g : R ⟶ R := f.hom
  have hf : μ[R] ≫ g = R ◁ g ≫ μ[R] := Mod.act_hom f
  have hm : Functor.LaxMonoidal.μ F R R ≫ F.map μ[R] = μ[R.obj] :=
    Sheaf.μ_comp_map_mul R
  have h : μ[R.obj] ≫ g.hom = R.obj ◁ g.hom ≫ μ[R.obj] := by
    calc
      _ = (Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]) ≫ F.map g := by
        rw [hm]
        rfl
      _ = Functor.LaxMonoidal.μ F R R ≫ F.map (R ◁ g ≫ μ[R]) := by
        rw [Category.assoc, ← F.map_comp, hf]
      _ = _ := by
        rw [F.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
          Category.assoc, hm]
        rfl
  have h' := congr_app h U
  exact congrArg (fun z => z.hom (a ⊗ₜ[ℤ] b)) h'

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
private lemma integral_one_sub_norm (a : continuousIntegers ℓ E) :
    ‖(1 - ℓ • a : continuousIntegers ℓ E).val‖ = 1 := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  have hp : ‖(ℓ : E)‖ < 1 := by
    have h : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ℓ : ℚ_[ℓ]))
    rw [h]
    exact Padic.norm_p_lt_one
  have ha : ‖a.val‖ ≤ 1 := by
    exact_mod_cast a.property
  have hsmall : ‖ℓ • a.val‖ < 1 := by
    rw [nsmul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ha).trans_lt hp
  change ‖1 - ℓ • a.val‖ = 1
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp only [norm_one, norm_neg, max_eq_left hsmall.le]
  · simpa only [norm_one, norm_neg] using hsmall.ne.symm

private theorem integral_continuous_unit {S : Type*} [TopologicalSpace S]
    (a : C(S, continuousIntegers ℓ E)) : IsUnit (1 - ℓ • a) := by
  let d : C(S, continuousIntegers ℓ E) := 1 - ℓ • a
  have hn (x : S) : ‖(d x).val‖ = 1 := integral_one_sub_norm ℓ E (a x)
  have hz (x : S) : (d x).val ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn x]
    exact one_ne_zero
  have hb (x : S) : (d x).val⁻¹ ∈ continuousIntegers ℓ E := by
    change ‖(d x).val⁻¹‖₊ ≤ 1
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_one, norm_inv, hn, inv_one, le_refl]
  let b : C(S, continuousIntegers ℓ E) := {
    toFun x := ⟨(d x).val⁻¹, hb x⟩
    continuous_toFun := Continuous.subtype_mk
      ((continuous_subtype_val.comp d.continuous).inv₀ hz) hb }
  have hdb : d * b = 1 := by
    ext x
    exact mul_inv_cancel₀ (hz x)
  exact ⟨Units.mkOfMulEqOne d b hdb, rfl⟩

private theorem integral_totallyDisconnected :
    TotallyDisconnectedSpace (continuousIntegers ℓ E) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  infer_instance
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonObj
private theorem continuousIntegralRegular_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (f : Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) ⟶
      Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E)))) :
    IsIso (𝟙 _ - ℓ • f) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X (continuousIntegers ℓ E))
  let g : R ⟶ R := f.hom
  have hpresheaf : IsIso (𝟙 R.obj - ℓ • g.hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let t : ULift.{u + 1} C(U.unop.left, continuousIntegers ℓ E) →
        ULift.{u + 1} C(U.unop.left, continuousIntegers ℓ E) := g.hom.app U
    change Function.Bijective (fun x => x - ℓ • t x)
    let a := t 1
    have hu : IsUnit (1 - ℓ • a) := by
      exact (integral_continuous_unit ℓ E a.down).map ULift.ringEquiv.symm.toRingHom
    have hex (x : ULift.{u + 1} C(U.unop.left, continuousIntegers ℓ E)) : t x = x * a := by
      simpa only [t, a, g, R, Mod.regular, _root_.mul_one] using
        continuousRegular_map_mul X _ f U x 1
    have heq : (fun x => x - ℓ • t x) = (· * (1 - ℓ • a)) := by
      funext x
      rw [hex, mul_sub, _root_.mul_one]
      simp only [nsmul_eq_mul, _root_.mul_assoc, Nat.cast_comm]
    rw [heq]
    exact IsUnit.isUnit_iff_mulRight_bijective.mp hu
  have hmapped : IsIso ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (𝟙 R - ℓ • g)) := by
    change IsIso (𝟙 R.obj - ℓ • g.hom)
    exact hpresheaf
  have hg : IsIso (𝟙 R - ℓ • g) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  have hf : IsIso ((Mod.forget R).map (𝟙 _ - ℓ • f)) := by
    change IsIso ((𝟙 _ - ℓ • f).hom)
    simpa only [Mod.sub_hom, Mod.nsmul_hom, Mod.id_hom', g, R, Mod.regular] using hg
  exact isIso_of_reflects_iso _ (Mod.forget R)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- One minus ℓ times an endomorphism of the regular integral module is invertible.
Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(blueprint: lem-weil-pbc-integral-scalar-contractive)

Proof: realize the pulled coefficient ring as the ring sheaf of continuous integral
functions. The comparison sends a function on a profinite test space to its composite
with the test projection. On a weakly contractible affine, the canonical arrow to the
profinite space of connected components is terminal in the Kan indexing category;
sheafification preserves its sections. Continuous functions into the integral ring
factor through connected components, since that ring is totally disconnected. Affine
weakly contractible covers then detect that the comparison is an isomorphism of rings.
Transport the regular module along this ring isomorphism. On every site object its
endomorphism is multiplication by its value a at one, by module linearity. The function
1-ℓa has norm one, since a is integral and the norm of ℓ is less than one. Its reciprocal
is integral and continuous, giving a unit in the continuous function ring. Multiplication
by this unit is bijective on sections, hence is an isomorphism of sheaves and module
objects. Conjugating back proves the assertion. Empty site objects cause no exception. -/
theorem integralRegular_one_sub_nsmul_isIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : R ⟶ condensedRingObj (integralCoeff ℓ E) X) [IsMonHom e] [IsIso e]
    (f : Mod.regular R ⟶ Mod.regular R) : IsIso (𝟙 _ - ℓ • f) := by
  have : TotallyDisconnectedSpace (continuousIntegers ℓ E) := integral_totallyDisconnected ℓ E
  let c := comparison X (continuousIntegers ℓ E)
  have : IsMonHom c := comparison_isMonHom X (continuousIntegers ℓ E)
  have : IsIso c := integralComparison_isIso X (continuousIntegers ℓ E)
  let d := e ≫ c
  have : IsMonHom d := inferInstance
  have : IsIso d := inferInstance
  let K := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (inv d)
  let j := Mod.regularIsoOfIsIso d
  let f' := j.inv ≫ K.map f ≫ j.hom
  have h' := continuousIntegralRegular_isIso ℓ E X f'
  have heq : j.hom ≫ (𝟙 _ - ℓ • f') ≫ j.inv = K.map (𝟙 _ - ℓ • f) := by
    simp [f', K, Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp]
  have : IsIso (K.map (𝟙 _ - ℓ • f)) := by
    rw [← heq]
    infer_instance
  have : IsIso ((𝟙 _ - ℓ • f).hom) :=
    inferInstanceAs (IsIso ((K.map (𝟙 _ - ℓ • f)).hom))
  have : IsIso ((Mod.forget R).map (𝟙 _ - ℓ • f)) := by
    change IsIso ((𝟙 _ - ℓ • f).hom)
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget R)
end AlgebraicGeometry.ProEtale.CondensedRing
