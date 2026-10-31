/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.PbcScalarRationalShift

/-! # Normalized finite-field stages and their coherence

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-stage-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section NestedFields
attribute [local irreducible] pbcRationalScalarHom
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual finite subfields, in a common ambient field; no algebraic closure
hypothesis is needed for this finite tower. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcCoefficientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalDerivedCategory l E.val T dim.out inv.out

/-- A nested finite subfield inclusion, with its actual algebra homomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcSubfieldInclusion {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    E.val →ₐ[Padic l] F.val := IntermediateField.inclusion h

/-- Identity inclusions are the actual algebra identity.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps fix every element of the subfield. -/
theorem pbcSubfieldInclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcSubfieldInclusion l Ω (le_refl E) = AlgHom.id (Padic l) E.val := by
  rfl

/-- Actual inclusions compose as direct inclusions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps send each subfield element to its same ambient scalar. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  rfl

/-- The actual rational tensor before literal identity normalization.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcStageRaw {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F :=
  pbcRationalScalarExtension l E.val F.val (pbcSubfieldInclusion l Ω h) T dim.out inv.out

/-- Equal coefficient fields use the literal identity functor.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcStageTransition {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F := by
  classical
  exact if e : E = F then e ▸ 𝟭 (pbcCoefficientStage l Ω T E)
    else pbcStageRaw l Ω T h

/-- Normalization uses precisely the ordinary tensor multiplication unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageNormalization {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcStageRaw l Ω T h ≅ pbcStageTransition l Ω T h := by
  classical
  by_cases e : E = F
  · subst F
    exact eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val E.val i T dim.out inv.out)
      (pbcSubfieldInclusion_id l Ω E)) ≪≫
        pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
          eqToIso (by unfold pbcStageTransition; rw [dif_pos rfl])
  · exact eqToIso (by simp only [pbcStageTransition, dif_neg e])

/-- Balancing, conjugated by the specified tensor units, is the chosen associator.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageAssociator {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    pbcStageTransition l Ω T h ⋙ pbcStageTransition l Ω T h' ≅
      pbcStageTransition l Ω T (h.trans h') :=
  isoWhiskerRight (pbcStageNormalization l Ω T h).symm _ ≪≫
    isoWhiskerLeft _ (pbcStageNormalization l Ω T h').symm ≪≫
    pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
    eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h')) ≪≫
    pbcStageNormalization l Ω T (h.trans h')

/-- Normalized tensor balancing satisfies both units and the four-field pentagon.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: on a K-flat complex both paths send the three nested scalar factors to
their product, with the same remaining tensor factor. Associativity gives equality
before localization. Multiplication by one gives each unit equation. The two
localizations preserve these equations, including coincident adjacent fields. -/
theorem pbcStageAssociator_laws :
    (∀ {E F G H : Padic.FiniteCoefficientFields l Ω}
      (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H)
      (K : pbcCoefficientStage l Ω T E),
      (pbcStageTransition l Ω T h'').map
          ((pbcStageAssociator l Ω T h h').hom.app K) ≫
        (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
      (pbcStageAssociator l Ω T h' h'').hom.app
          ((pbcStageTransition l Ω T h).obj K) ≫
        (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      HEq (pbcStageAssociator l Ω T (le_refl E) h)
        (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
      HEq (pbcStageAssociator l Ω T h (le_refl F))
        (Functor.rightUnitor (pbcStageTransition l Ω T h))) := by
  sorry

/-- Normalized transitions retain the canonical tensor shift comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
instance pbcStageTransitionShift {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcStageTransition l Ω T h).CommShift ℤ :=
  Functor.CommShift.ofIso (pbcStageNormalization l Ω T h) ℤ

/-- Literal normalization preserves addition and exactness with this shift.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: conjugating by the specified natural tensor-unit isomorphism preserves
addition and distinguished image triangles. Its transported shift is the one
just defined, so the triangle's last arrow is retained. -/
theorem pbcStageExact {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcStageTransition l Ω T h).Additive ∧
      (pbcStageTransition l Ω T h).IsTriangulated := by
  have hcompat := Functor.CommShift.ofIso_compatibility
    (pbcStageNormalization l Ω T h) ℤ
  have : NatTrans.CommShift (pbcStageNormalization l Ω T h).hom ℤ := hcompat
  exact ⟨Functor.additive_of_iso (pbcStageNormalization l Ω T h),
    Functor.isTriangulated_of_iso (pbcStageNormalization l Ω T h)⟩

private theorem scalarEqToIso_shift
    {C D I : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : I → C ⥤ D) (s : ∀ i, (F i).CommShift ℤ) {i j : I} (h : i = j) :
    letI := s i
    letI := s j
    NatTrans.CommShift (eqToIso (congrArg F h)).hom ℤ := by
  subst j
  change NatTrans.CommShift (𝟙 (F i)) ℤ
  infer_instance

/-- The specified associators commute with every integer shift.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: balancing is multiplication on shifted tensor terms, with the same signs
on both sides. Universal derived counits and rational tensor generation descend
the equation. Conjugation by the tensor units preserves it. -/
theorem pbcStageAssociatorShift {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    NatTrans.CommShift (pbcStageAssociator l Ω T h h').hom ℤ := by
  have : NatTrans.CommShift (pbcStageNormalization l Ω T h).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (pbcStageNormalization l Ω T h) ℤ
  have : NatTrans.CommShift (pbcStageNormalization l Ω T h').hom ℤ :=
    Functor.CommShift.ofIso_compatibility (pbcStageNormalization l Ω T h') ℤ
  have : NatTrans.CommShift (pbcStageNormalization l Ω T (h.trans h')).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (pbcStageNormalization l Ω T (h.trans h')) ℤ
  have : NatTrans.CommShift (pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out).hom ℤ :=
    scalarRationalComp_shift l E.val F.val (pbcSubfieldInclusion l Ω h) T
      G.val (pbcSubfieldInclusion l Ω h')
  have : NatTrans.CommShift (eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h'))).hom ℤ := by
    exact scalarEqToIso_shift
      (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (fun i ↦ pbcRationalScalarShift l E.val G.val i T)
      (pbcSubfieldInclusion_comp l Ω h h')
  unfold pbcStageAssociator
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance
end NestedFields
end AlgebraicGeometry.Scheme
