/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitStrictComparison
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Regular completed units and their strict reductions

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap
namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalObject integralObject rationalSource modelScalar modelUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pushforward_unit_iso
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {S : Sheaf J RingCat.{u + 1}} {R : Sheaf K RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) [IsIso φ] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  let G := SheafOfModules.toSheaf S ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}
  have : IsIso (G.map (SheafOfModules.unitToPushforwardObjUnit φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (φ.hom.app V)
    exact (ConcreteCategory.isIso_iff_bijective (φ.hom.app V)).mp inferInstance
  exact isIso_of_reflects_iso (SheafOfModules.unitToPushforwardObjUnit φ) G

private theorem eqToHom_ring_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (h : R = S) (V : Cᵒᵖ) (x : R.obj.obj V) :
    HEq ((eqToHom h).hom.app V x) x := by
  subst S
  rfl

private def finiteUnit (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) := by
  unfold systemUnit coefficientSequenceEvaluation
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  let := pushforward_unit_iso φ
  exact (asIso (SheafOfModules.unitToPushforwardObjUnit φ)).symm

private theorem finiteUnit_sections (W : Scheme.{u}) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V) :
    HEq ((finiteUnit l E W n).hom.val.app V x) x := by
  have hi (z : (SheafOfModules.unit (integralCoefficientSheaf l E W n)).val.obj V) :
      HEq ((finiteUnit l E W n).inv.val.app V z) z := by
    unfold systemUnit coefficientSequenceEvaluation
    dsimp only [finiteUnit]
    change HEq (((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app V) z) z
    exact eqToHom_ring_apply _ V z
  have h := congrArg (fun k ↦ k.val.app V x) (finiteUnit l E W n).hom_inv_id
  change ((finiteUnit l E W n).inv.val.app V)
    (((finiteUnit l E W n).hom.val.app V) x) = x at h
  exact (hi _).symm.trans (heq_of_eq h)

/-- The regular completed unit has its canonical strict quotient-system presentation.

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Definition 6.5.1; the first three
steps of lem-pur-completed-unit-pullback-tower.
(blueprint: lem-pur-completed-unit-reduction).

Proof: identify the evaluated regular module by the inverse of the canonical
unit-to-pushforward-unit map for the equality of its coefficient ring with the
actual finite ring. Equality induction gives its section formula; the inverse
identities give the corresponding formula for its inverse. Apply the strict
regular-system comparison to these finite identifications. Existing constant
coefficient constructibility gives derived completeness of the integral unit.
Stalkwise invertibility gives invertibility on global sections, so normalized
reconstruction makes the actual adjunction unit invertible. Compose that unit
isomorphism with the total limit of the strict comparison. Its augmentation
equality is then definitional. Empty schemes and exponent one are covered by
the same constructions. -/
theorem completedUnitReduction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (W : Scheme.{u})
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w)) :
    Nonempty (Reduction l E W (calculus l E W)) := by
  obtain ⟨c, hc⟩ := completedUnitStrictComparison l E D hl W (calculus l E W)
    (finiteUnit l E W) (finiteUnit_sections l E W)
  have htop : IsUnit (l : Γ(W, ⊤)) := by
    apply W.toRingedSpace.isUnit_of_isUnit_germ ⊤ (l : Γ(W, ⊤))
    intro w hw
    simpa only [map_natCast] using hW w
  have hcomplete := (integralConstantCoefficient_constructible l E W D hl).2.2.1
  let := (purNormalizedReconstruction l E W htop (calculus l E W)).2 _ hcomplete
  let a := asIso ((calculus l E W).adjunction.unit.app
    (integralConstantCoefficientObject l E W)) ≪≫
      (coefficientSequenceLimit l E W).mapIso c
  exact ⟨⟨finiteUnit l E W, finiteUnit_sections l E W, c, hc, a, rfl⟩⟩

end WeilConjectures.CompletedUnitPullback
