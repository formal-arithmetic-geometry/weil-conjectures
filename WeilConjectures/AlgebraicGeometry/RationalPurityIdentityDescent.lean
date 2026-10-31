/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPurityPresentationData

/-! # Identity comparisons under PBC descent -/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option linter.all false
universe u w w₀ u₀ u₁ v₀ v₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  AlgebraicGeometry.Scheme.pbcRationalScalarHom
  AlgebraicGeometry.Scheme.pbcPurityTwisted AlgebraicGeometry.Scheme.pbcPurityCompact
  AlgebraicGeometry.Scheme.pbcPurityTwistedAmbient
  AlgebraicGeometry.Scheme.pbcPurityCompactAmbient
  AlgebraicGeometry.Scheme.pbcPurityStageA AlgebraicGeometry.Scheme.pbcPurityStageC
  AlgebraicGeometry.Scheme.pbcPurityStageTwisted
  AlgebraicGeometry.Scheme.pbcPurityStageCompact
  AlgebraicGeometry.Scheme.pbcPurityScalarNormalization
  AlgebraicGeometry.Scheme.pbcPurityTwistedScalar
  AlgebraicGeometry.Scheme.pbcPurityCompactScalar
  AlgebraicGeometry.Scheme.pbcPurityTateModel
  AlgebraicGeometry.Scheme.pbcPurityDerivedScalarModel
  purCoefficientModel integralSheafTwist completedDerivedScalarExtension pbcTateAmbient
  purScalarModel integralTwistOrdinaryBeta pbcPurityTateScalarModel
  pbcPurityTateScalarComponent pbcActualCompletedPull

/-- All descent clauses other than exactness follow from the stage-system API. -/
private theorem pbcPurityFormalDescent
    {I : Type w₀} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₀} [∀ i, Category.{v₀} (C i)]
    {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
    {S : StageSystem C} {S' : StageSystem D}
    [Preadditive S.PairCategory] [Preadditive S'.PairCategory]
    [HasZeroObject S.PairCategory] [HasZeroObject S'.PairCategory]
    [HasShift S.PairCategory ℤ] [HasShift S'.PairCategory ℤ]
    [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
    [∀ n : ℤ, (shiftFunctor S'.PairCategory n).Additive]
    [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]
    (H : StageSystem.Morphism S S') (he : StageSystem.Morphism.ExactDescent H) :
    StageSystem.Morphism.DescentSpec H := by
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · intro K L M hK hL u
    exact H.functor_map_mkHom hK hL u
  · intro G J τ K
    exact StageSystem.Morphism.descNatTrans_app τ K
  · intro G J τ τ' h
    apply NatTrans.ext
    funext K
    exact congrArg ((S'.ι K.stage).map) (h K.stage K.obj)
  · exact StageSystem.Morphism.descNatTrans_id
  · exact fun G J L τ τ' ↦ StageSystem.Morphism.descNatTrans_comp τ τ'

section FormalIdentityComparison
variable {I : Type w₀} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₀} [∀ i, Category.{v₀} (C i)]
    {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
    {S : StageSystem C} {S' : StageSystem D} (H : StageSystem.Morphism S S')

private theorem pbcPurityIdentityComponent (K : S.PairCategory) :
    𝟙 (H.functor.obj K) =
      (CategoryTheory.Functor.whiskerRight (𝟙 (H.Φ K.stage)) (S'.ι K.stage)).app K.obj := by
  simp only [CategoryTheory.Functor.whiskerRight_id', NatTrans.id_app,
    CategoryTheory.Functor.comp_obj, StageSystem.Morphism.functor_obj, StageSystem.ι_obj]

private theorem pbcPurityIdentityCommonStage {i j n : I} (hK : i ≤ n) (hL : j ≤ n)
    (K : C i) (L : C j) (u : (S.T hK).obj K ⟶ (S.T hL).obj L) :
    ((H.β hK).hom.app K ≫ (H.Φ n).map u ≫ (H.β hL).inv.app L) ≫
        (S'.T hL).map (𝟙 ((H.Φ j).obj L)) =
      (S'.T hK).map (𝟙 ((H.Φ i).obj K)) ≫
        ((H.β hK).hom.app K ≫ (H.Φ n).map u ≫ (H.β hL).inv.app L) := by
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

end FormalIdentityComparison

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

attribute [local irreducible] StageSystem.Morphism.functor StageSystem.ι
  PbcPurityDescent

/-- The identity comparison of the actual twisted system satisfies formal descent.

Source: original parent proof Step 5 and the current coefficient-change proof,
(blueprint: lem-pur-pbc-identity-descent).

Proof: exactness supplies the only nonformal clause. The remaining DescentSpec
clauses are the published representative, component, extensionality, identity and
composition laws. The identity comparison has the required finite-stage components
because whiskering preserves identities and the descended functor and inclusion
have the specified pair objects. Hom and inverse are the same identity map. In the
common-stage equation the two identity components cancel, leaving the identical
representative map. No adjunction or new scalar-coherence property is asserted. -/
theorem pbcPurityIdentityDescent
    (he : StageSystem.Morphism.ExactDescent (pbcPurityTwistedSystem l Ω f c d)) :
    PbcPurityDescent l Ω f c d (pbcPurityTwistedSystem l Ω f c d)
      (fun E ↦ Iso.refl _) (Iso.refl _) := by
  let H := pbcPurityTwistedSystem l Ω f c d
  have hdesc : StageSystem.Morphism.DescentSpec H := pbcPurityFormalDescent H he
  unfold PbcPurityDescent
  refine ⟨hdesc, hdesc, ?_, ?_⟩
  · intro K
    suffices hc : _ by exact ⟨hc, hc⟩
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      NatTrans.id_app, Iso.refl_hom] using pbcPurityIdentityComponent H K
  · intro E F M hE hF K L u
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      Iso.refl_inv, NatTrans.id_app] using
        pbcPurityIdentityCommonStage H hE hF K L u

end AlgebraicGeometry.Scheme
