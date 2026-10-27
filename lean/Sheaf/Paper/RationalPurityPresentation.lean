/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.RationalPurityPresentationData
import Sheaf.Paper.RationalPurityFiniteAdjunction
import Sheaf.Paper.RationalPurityTwistedExact
import Sheaf.Paper.RationalPurityIdentityDescent

/-! # Coefficient transitivity and retracts of PBC smooth purity

Source: prop-pur-rational-purity-transitivity-summands, proof Steps 1--7.
The scalar and presentation APIs are publicly re-exported with unchanged declarations.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option linter.all false
set_option linter.unusedVariables false
universe u w w₀ u₀ u₁ v₀ v₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures AlgebraicGeometry.Scheme
open scoped TensorProduct

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

/-- Extending the identity comparison to Karoubi objects preserves its invertibility. -/
private theorem pbcPurityIdentityKaroubi
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) (K : Idempotents.Karoubi C) :
    IsIso (((Idempotents.functorExtension₂ C D).map (𝟙 F)).app K) := by
  rw [CategoryTheory.Functor.map_id]
  change IsIso (𝟙 _)
  infer_instance

/-- A component of the image of any natural isomorphism is an isomorphism. -/
private theorem pbcPurityKaroubiComparison
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ D} (γ : F ≅ G) (K : Idempotents.Karoubi C) :
    IsIso (((Idempotents.functorExtension₂ C D).map γ.hom).app K) := by
  exact (((Idempotents.functorExtension₂ C D).mapIso γ).app K).isIso_hom

/-- An identity comparison restricts to the identity along any actual retract. -/
private theorem pbcPurityIdentityRetract
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) {J K : C} (i : J ⟶ K) (r : K ⟶ J) (hi : i ≫ r = 𝟙 J) :
    F.map i ≫ 𝟙 (F.obj K) ≫ F.map r = 𝟙 (F.obj J) ∧
      F.map i ≫ 𝟙 (F.obj K) ≫ F.map r = 𝟙 (F.obj J) := by
  simp only [CategoryTheory.Category.id_comp, ← CategoryTheory.Functor.map_comp, hi,
    CategoryTheory.Functor.map_id, and_self]

/-- Naturality restricts a comparison along any specified retract. -/
private theorem pbcPurityRetractNatTrans
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ D} (τ : F ⟶ G) {J K : C}
    (i : J ⟶ K) (r : K ⟶ J) (hi : i ≫ r = 𝟙 J) :
    F.map i ≫ τ.app K ≫ G.map r = τ.app J := by
  calc
    F.map i ≫ τ.app K ≫ G.map r = (F.map i ≫ τ.app K) ≫ G.map r :=
      (CategoryTheory.Category.assoc _ _ _).symm
    _ = (τ.app J ≫ G.map i) ≫ G.map r :=
      congrArg (fun v ↦ v ≫ G.map r) (τ.naturality i)
    _ = τ.app J ≫ (G.map i ≫ G.map r) := CategoryTheory.Category.assoc _ _ _
    _ = τ.app J ≫ G.map (i ≫ r) :=
      congrArg (fun v ↦ τ.app J ≫ v) (G.map_comp i r).symm
    _ = τ.app J ≫ G.map (𝟙 J) := congrArg (fun v ↦ τ.app J ≫ G.map v) hi
    _ = τ.app J ≫ 𝟙 (G.obj J) := congrArg (fun v ↦ τ.app J ≫ v) (G.map_id J)
    _ = τ.app J := CategoryTheory.Category.comp_id _

/-- Both directions of an isomorphism restrict along the same retract. -/
private theorem pbcPurityRetractComparison
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ D} (γ : F ≅ G) {J K : C}
    (i : J ⟶ K) (r : K ⟶ J) (hi : i ≫ r = 𝟙 J) :
    (F.map i ≫ γ.hom.app K ≫ G.map r = γ.hom.app J) ∧
      (G.map i ≫ γ.inv.app K ≫ F.map r = γ.inv.app J) := by
  exact ⟨pbcPurityRetractNatTrans γ.hom i r hi,
    pbcPurityRetractNatTrans γ.inv i r hi⟩

section FormalIdentityComparison
variable {I : Type w₀} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₀} [∀ i, Category.{v₀} (C i)]
    {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
    {S : StageSystem C} {S' : StageSystem D} (H : StageSystem.Morphism S S')

private theorem pbcPurityIdentitySquare {i j : I} (h : i ≤ j) (K : C i) :
    (S'.T h).map (𝟙 ((H.Φ i).obj K)) ≫ (H.β h).hom.app K =
      (H.β h).hom.app K ≫ 𝟙 ((H.Φ j).obj ((S.T h).obj K)) := by
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]

private theorem pbcPurityIdentityTransitivity {i j n : I}
    (h : i ≤ j) (k : j ≤ n) (K : C i) :
    ((S'.assoc h k).hom.app ((H.Φ i).obj K) ≫
        (S'.T (h.trans k)).map (𝟙 ((H.Φ i).obj K)) ≫
        (H.β (h.trans k)).hom.app K =
      (S'.T k).map ((S'.T h).map (𝟙 ((H.Φ i).obj K))) ≫
        (S'.T k).map ((H.β h).hom.app K) ≫
        (H.β k).hom.app ((S.T h).obj K) ≫
        (H.Φ n).map ((S.assoc h k).hom.app K)) ∧
    ((S'.assoc h k).hom.app ((H.Φ i).obj K) ≫
        (S'.T (h.trans k)).map (𝟙 ((H.Φ i).obj K)) ≫
        (H.β (h.trans k)).hom.app K =
      (S'.assoc h k).hom.app ((H.Φ i).obj K) ≫
        (H.β (h.trans k)).hom.app K ≫
        𝟙 ((H.Φ n).obj ((S.T (h.trans k)).obj K))) := by
  constructor
  · simpa only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]
      using (H.coh h k K).symm
  · simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]

end FormalIdentityComparison

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
    [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
    [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
    [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
    [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
    [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
    (d : ℕ) [fsm : SmoothOfRelativeDimension d f]

attribute [local irreducible] StageSystem.Morphism.functor StageSystem.ι
  PbcPurityTransitivity PbcPurityDescent Idempotents.functorExtension₂
  StageSystem.PairCategory.categoryStruct

include Xbase Ybase Xsep Ysep Xft Xqc Yft Yqc fbase fsep fft fqc fsm hl in
/-- The actual rational purity isomorphisms admit their normalized coefficient square,
its tensor-associator transitivity equation, compatible Qbar descent and restriction
to every rational or Qbar idempotent summand.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-field-extension,
prop-pur-rational-purity-transitivity-summands, proof Steps 1--7
(blueprint: prop-pur-rational-purity-transitivity-summands).

Proof:
1. Derive the Noetherian, dimension and invertibility instances from the source
   finite-field geometry. The finite-stage normalized purity-adjunction lemma
   identifies twisted pullback itself as a right adjoint of the specified actual
   compact support, with its coefficient comparison fixed by the counit square.
2. Present the exceptional family in these twisted right-adjoint coordinates:
   G is the already constructed twisted StageSystem morphism, and gamma is the
   identity. Its exceptional specification is precisely that counit square. The
   first transitivity equation is the symmetry of the stage coherence equation;
   the second is reflexivity after removing the identity gamma components.
3. Apply the exact-descent bridge to this coherent family. Its representative
   formula, component formula, extensionality, identity and composition clauses
   are the published StageSystem descent lemmas, which give DescentSpec. Choose
   the identity comparison after descent as well. Both component formulas are
   preservation of identities by the finite-stage inclusion. The common-stage
   inverse naturality equation reduces to the identical representative map.
4. At both coefficient stages, functorExtension₂ carries the identity natural
   transformation to the identity, whose components are isomorphisms. For a
   retract i followed by r equal to the identity, functoriality gives
   H(i) followed by H(r) equal to the identity, for hom and inverse. Thus every
   required Karoubi and actual-retract clause holds, including rational
   idempotents without integral idempotent representatives. -/
theorem rationalPurityTransitivitySummands :
    PbcRationalPurityConclusion l Ω D hl f d := by
  letI := (pbcPurityGeometricBounds l D hl X).1
  letI := (pbcPurityGeometricBounds l D hl Y).1
  letI : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.1⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.1⟩
  letI : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.2⟩
  letI : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.2⟩
  change ∀ c : Compactification f, PbcPurityCoefficientConclusion l Ω f c d
  intro c
  let H := pbcPurityTwistedSystem l Ω f c d
  obtain ⟨adj, hmate⟩ := pbcPurityFiniteAdjunction l Ω f c d D hl
  have hex : StageSystem.Morphism.ExactDescent H := by
    dsimp only [H, pbcPurityTwistedSystem]
    exact pbcPurityTwisted_exactDescent l Ω f c d
      (pbcPurityStageA_coherence l Ω f c d)
  unfold PbcPurityCoefficientConclusion
  -- Use the purity adjunction to present the exceptional right adjoint by H itself.
  -- The purity comparison is then the identity in these counit-compatible coordinates.
  refine ⟨H, ⟨adj, hmate⟩, (fun E ↦ Iso.refl _), ?_, ?_, ?_, ?_,
    Iso.refl _, ?_, ?_, ?_⟩
  · intro E F h K
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      NatTrans.id_app, Iso.refl_hom] using pbcPurityIdentitySquare H h K
  · unfold PbcPurityTransitivity
    intro E F L h k K
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      NatTrans.id_app, Iso.refl_hom] using
      pbcPurityIdentityTransitivity H h k K
  · intro E K e he
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      NatTrans.id_app, Iso.refl_hom] using
      pbcPurityIdentityKaroubi (pbcPurityStageTwisted l Ω f c d E) ⟨K, e, he⟩
  · intro E J K i r hi
    simpa only [H, pbcPurityTwistedSystem, CategoryTheory.Functor.comp_obj,
      NatTrans.id_app, Iso.refl_hom, Iso.refl_inv] using
      pbcPurityIdentityRetract (pbcPurityStageTwisted l Ω f c d E) i r hi
  · exact pbcPurityIdentityDescent l Ω f c d hex
  · intro K e he
    exact pbcPurityKaroubiComparison
      (Iso.refl (pbcPurityTwistedSystem l Ω f c d).functor) ⟨K, e, he⟩
  · intro J K i r hi
    exact pbcPurityRetractComparison
      (Iso.refl (pbcPurityTwistedSystem l Ω f c d).functor) i r hi

end AlgebraicGeometry.Scheme
