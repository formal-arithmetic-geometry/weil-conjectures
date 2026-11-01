/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionCoefficientUnitData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularSequenceNormalized

/-! Normalization of the actual coefficient unit. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

private theorem unitToPushforwardObjUnit_isIso
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{u + 1}} {R : Sheaf K RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    [IsIso φ] : IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  let G := SheafOfModules.toSheaf S ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}
  have hG : IsIso (G.map (SheafOfModules.unitToPushforwardObjUnit φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (φ.hom.app V)
    exact (ConcreteCategory.isIso_iff_bijective (φ.hom.app V)).mp inferInstance
  exact isIso_of_reflects_iso (SheafOfModules.unitToPushforwardObjUnit φ) G

private theorem eqToHom_ring_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (h : R = S) (V : Cᵒᵖ)
    (x : R.obj.obj V) : HEq ((eqToHom h).hom.app V x) x := by
  subst S
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

/-- The regular sequence-ring module in degree zero has derived quotient transitions.
Source: Stacks 06YY and 0941; finite adjunction realization proof step 9
(blueprint: lem-sf-coefficient-unit-normalization).
Proof: evaluation of the regular sequence module is the regular finite module.
Its horizontal restriction is the quotient ring homomorphism on every section.
The regular module is flat, so derived extension along this quotient is ordinary
extension, and multiplication identifies it with the target regular module.
The universal extension/restriction adjunction then identifies precomposition by
this actual transition with a bijection into every derived target. These are
exactly the bijections in IsNormalizedCoefficientSequence, for all m >= n,
including the identity quotient. -/
theorem coefficientUnit_normalized (W : Scheme.{u}) :
    IsNormalizedCoefficientSequence l E W (coefficientUnit (l := l) (E := E) W) := by
  let b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj
      (CompletedUnitPullback.systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) := fun n ↦ by
    unfold CompletedUnitPullback.systemUnit coefficientSequenceEvaluation
    let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
    letI : IsIso (SheafOfModules.unitToPushforwardObjUnit φ) :=
      unitToPushforwardObjUnit_isIso φ
    exact (asIso (SheafOfModules.unitToPushforwardObjUnit φ)).symm
  have hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj
        (CompletedUnitPullback.systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x := by
    intro n V x
    have hi (z : (SheafOfModules.unit (integralCoefficientSheaf l E W n)).val.obj V) :
        HEq ((b n).inv.val.app V z) z := by
      unfold b
      change HEq ((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app V z) z
      exact eqToHom_ring_apply _ V z
    have h := congrArg (fun k ↦ k.val.app V x) (b n).hom_inv_id
    change ((b n).inv.val.app V) (((b n).hom.val.app V) x) = x at h
    exact (hi _).symm.trans (heq_of_eq h)
  change IsNormalizedCoefficientSequence l E W
    (CompletedUnitPullback.systemObject l E W)
  exact CompletedUnitPullback.regularSequenceNormalized l E W b hb

end WeilConjectures.FiniteAdjunctionDiagram
