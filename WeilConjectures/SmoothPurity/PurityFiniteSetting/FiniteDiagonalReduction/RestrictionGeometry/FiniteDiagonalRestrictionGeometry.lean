/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationRestrictionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionEtaleRestriction

/-! # The two geometric operations in diagonal open restriction

Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
namespace RestrictionGeometry
open SectionRestriction
attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

private theorem iso_square_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {A' B' : D} (a : A ≅ B) (n : F.obj B ≅ B')
    (s : F.obj A ≅ A') (b : A' ≅ B') (h : F.mapIso a ≪≫ n = s ≪≫ b) :
    F.map a.hom ≫ n.hom = s.hom ≫ b.hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using congrArg Iso.hom h

variable {X Y : Scheme.{u}}
variable (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)

/-- The diagonal as a smooth section pair.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def diagonalPair : Pair X d where
  V := pullback f f
  g := pullback.fst f f
  s := pullback.diagonal f
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  closed := inferInstance
  section_eq := pullback.diagonal_fst f

/-- The diagonal pair after changing only its base to the source open.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def mixedPair : Pair U.1.toScheme d where
  V := pullback (U.1.ι ≫ f) f
  g := pullback.fst (U.1.ι ≫ f) f
  s := pullback.lift (𝟙 _) U.1.ι (Category.id_comp _)
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  closed := inferInstance
  section_eq := pullback.lift_fst _ _ _

/-- The map to the original self-product.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def mixedMap : (mixedPair d f U).V ⟶ pullback f f :=
  pullback.lift (W := pullback (U.1.ι ≫ f) f) (f := f) (g := f)
    (pullback.fst (U.1.ι ≫ f) f ≫ U.1.ι) (pullback.snd (U.1.ι ≫ f) f) (by
      rw [Category.assoc, pullback.condition])

/-- This is the Cartesian base change of the first projection.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def sourceSquare : BaseChange U.1.ι (mixedPair d f U) (diagonalPair d f) where
  map := mixedMap d f U
  square := by
    apply IsPullback.of_right (h₁₂ := pullback.snd f f) (h₂₂ := f)
      (v₁₃ := f) ?_ ?_ (IsPullback.of_hasPullback f f).flip
    · simpa only [mixedMap, mixedPair, pullback.lift_snd] using
        (IsPullback.of_hasPullback (U.1.ι ≫ f) f).flip
    · simp only [mixedMap, mixedPair, pullback.lift_fst]
  section_eq := by
    apply pullback.hom_ext <;> simp [mixedPair, mixedMap, diagonalPair, Category.assoc]

/-- Restricting the second factor gives an open neighbourhood of the section.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def ambientMap : pullback (f.resLE V.1 U.1 hUV) (f.resLE V.1 U.1 hUV) ⟶
    (mixedPair d f U).V :=
  pullback.lift (W := pullback (f.resLE V.1 U.1 hUV) (f.resLE V.1 U.1 hUV))
    (f := U.1.ι ≫ f) (g := f)
    (pullback.fst (f.resLE V.1 U.1 hUV) (f.resLE V.1 U.1 hUV))
    (pullback.snd (f.resLE V.1 U.1 hUV) (f.resLE V.1 U.1 hUV) ≫ U.1.ι) (by
      rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hUV,
        ← Category.assoc, pullback.condition, Category.assoc])

omit [LocallyOfFiniteType f] in
/-- The ambient open is the pullback of the source-open inclusion.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
theorem ambientSquare :
    IsPullback (ambientMap d f U V hUV)
      (pullback.snd (f.resLE V.1 U.1 hUV) (f.resLE V.1 U.1 hUV))
      (pullback.snd (U.1.ι ≫ f) f) U.1.ι := by
  dsimp only [ambientMap, mixedPair]
  let h := f.resLE V.1 U.1 hUV
  have hc (c : PullbackCone (pullback.snd (U.1.ι ≫ f) f) U.1.ι) :
      (c.fst ≫ pullback.fst (U.1.ι ≫ f) f) ≫ h = c.snd ≫ h := by
    apply (cancel_mono V.1.ι).mp
    simp only [Category.assoc, h, Scheme.Hom.resLE_comp_ι]
    rw [pullback.condition, ← Category.assoc, c.condition, Category.assoc]
  let l (c : PullbackCone (pullback.snd (U.1.ι ≫ f) f) U.1.ι) :=
    pullback.lift (f := h) (g := h)
      (c.fst ≫ pullback.fst (U.1.ι ≫ f) f) c.snd (hc c)
  refine ⟨⟨pullback.lift_snd _ _ _⟩, ⟨PullbackCone.IsLimit.mk _ l ?_ ?_ ?_⟩⟩
  · intro c
    apply pullback.hom_ext
    · simp [l, h, Category.assoc]
    · simpa [l, h, Category.assoc] using c.condition.symm
  · intro c
    simp [l, h]
  · intro c m hm₁ hm₂
    apply pullback.hom_ext
    · have he := congrArg (fun k ↦ k ≫ pullback.fst (U.1.ι ≫ f) f) hm₁
      simpa [l, h, Category.assoc] using he
    · simpa [l, h] using hm₂

variable [AlgebraicGeometry.IsNoetherian X]
variable [SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV)]

/-- The actual étale map of section pairs; its centres are Cartesian.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def ambientRestriction : EtaleMap
    (diagonalPair d (f.resLE V.1 U.1 hUV)) (mixedPair d f U) :=
  letI : IsOpenImmersion (ambientMap d f U V hUV) :=
    MorphismProperty.of_isPullback (ambientSquare d f U V hUV).flip inferInstance
  letI : QuasiCompact (ambientMap d f U V hUV) :=
    MorphismProperty.of_isPullback (ambientSquare d f U V hUV).flip inferInstance
  { map := ambientMap d f U V hUV
    etale := by
      change Etale (ambientMap d f U V hUV)
      infer_instance
    separated := by
      change IsSeparated (ambientMap d f U V hUV)
      infer_instance
    quasiCompact := by
      change QuasiCompact (ambientMap d f U V hUV)
      infer_instance
    over_eq := by simp [ambientMap, diagonalPair, mixedPair]
    section_eq := by
      apply pullback.hom_ext <;> simp [ambientMap, diagonalPair, mixedPair, Category.assoc]
    centres := by
      change IsPullback (pullback.diagonal (f.resLE V.1 U.1 hUV)) (𝟙 U.1.toScheme)
        (ambientMap d f U V hUV) (mixedPair d f U).s
      apply IsPullback.of_vert_isIso_mono
      exact ⟨by
        apply pullback.hom_ext <;> simp [ambientMap, mixedPair, Category.assoc]⟩ }

variable (P : PurityFiniteSetting.{u})
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The source-section restriction is smooth base change followed by the inverse
of restriction from the open neighbourhood of the section.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def sourceRestriction :=
  baseComparison P (f ≫ aY) ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
      (sourceSquare d f U) ≪≫
    (restriction P ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
      (ambientRestriction d f U V hUV)).symm

/-- The same construction on the actual associated-graded normal cones.
Source: orientation charts, Steps 1--3.
(blueprint: lem-pur-finite-diagonal-restriction-geometry). -/
def normalRestriction :=
  baseComparison P (f ≫ aY) ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
      (normalBaseChange P (f ≫ aY) ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
        (sourceSquare d f U)) ≪≫
    (restriction P ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
      (normalEtaleMap P ((f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY)
        (ambientRestriction d f U V hUV))).symm

omit [AlgebraicGeometry.IsNoetherian X] in
private theorem chartDelta_eq_delta :
    P.chartDiagonalDelta d f aY = delta P (f ≫ aY) (diagonalPair d f) := by
  apply (Dnc.existsUnique_dncInvariance P d (pullback.fst f f) (f ≫ aY)
    (pullback.diagonal f) (pullback.diagonal_fst f)).unique
  · exact (Dnc.existsUnique_dncInvariance P d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f)).exists.choose_spec
  · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d
      (pullback.fst f f) (f ≫ aY) (pullback.diagonal f) (pullback.diagonal_fst f))).1

/-- The normalized DNC factor commutes with the two actual geometric operations.
Source: orientation charts Steps 1--3; SectionRestriction.coherence.
(blueprint: lem-pur-finite-diagonal-restriction-geometry).
Proof: apply NormalizedBase to the Cartesian mixed pair, and Endpoints to its
open neighbourhood. Compose the two squares and cancel their shared normal
restriction. Uniqueness identifies the selected chart delta with the pair delta.
All constructions and cancellations also apply to empty opens and rank zero. -/
theorem delta_square :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.1.ι).leftDerivedFunctor.map
        (P.chartDiagonalDelta d f aY).hom ≫
      (normalRestriction d f U V hUV P aY).hom =
    (sourceRestriction d f U V hUV P aY).hom ≫
      (P.chartDiagonalDelta d (f.resLE V.1 U.1 hUV) (V.1.ι ≫ aY)).hom := by
  let h := f.resLE V.1 U.1 hUV
  let aU := h ≫ V.1.ι ≫ aY
  have ha : U.1.ι ≫ (f ≫ aY) = aU := by
    dsimp only [aU, h]
    simp only [← Category.assoc, Scheme.Hom.resLE_comp_ι]
  have C := SectionRestriction.coherence P
  have hb := (C.2.2.2.1 X U.1.toScheme (f ≫ aY) aU U.1.ι ha d
    (diagonalPair d f) (mixedPair d f U) (sourceSquare d f U)).2.2
  have he := (C.2.2.1 U.1.toScheme aU d (diagonalPair d h)
    (mixedPair d f U) (ambientRestriction d f U V hUV)).2.2
  let rn := restriction P aU
    (normalEtaleMap P aU (ambientRestriction d f U V hUV))
  let rs := restriction P aU (ambientRestriction d f U V hUV)
  have he₂ := congrArg (fun e ↦ rs.symm ≪≫ e ≪≫ rn.symm) he
  simp only [rs, rn, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
    Iso.symm_self_id_assoc] at he₂
  have hi := congrArg (fun e ↦ e ≪≫ rn.symm) hb
  simp only [rn, Iso.trans_assoc] at hi
  rw [← he₂] at hi
  have hi' := hi.trans (Iso.trans_assoc
    (baseComparison P (f ≫ aY) aU (sourceSquare d f U)) rs.symm
    (delta P aU (diagonalPair d h))).symm
  rw [chartDelta_eq_delta d f P aY,
    chartDelta_eq_delta d h P (V.1.ι ≫ aY)]
  dsimp only [aU, h, rs, normalRestriction, sourceRestriction, invariant, diagonalPair]
    at hi' ⊢
  exact iso_square_hom _ _ _ _ _ hi'

end RestrictionGeometry
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
