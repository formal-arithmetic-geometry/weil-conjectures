/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData
import WeilConjectures.DeligneLaumon.CondensedWeilAbelian
import WeilConjectures.DeligneLaumon.WeilRepresentationSubobjects
import Mathlib.CategoryTheory.Abelian.Transfer

/-! # Completing the categorical consequences of normalized descent
Source: Weil II (1.1.12), proof steps 8--9.
(blueprint: lem-dl-a1-normalized-weil-assertions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

private theorem abelian_target {C R : Type*} [Category C] [Category R]
    [Abelian C] [Preadditive R] (e : C ≌ R) : Nonempty (Abelian R) := by
  let : HasFiniteProducts R :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  exact ⟨abelianOfEquivalence e.inverse⟩

private theorem equivalence_exact {C R : Type*} [Category C] [Category R] (e : C ≌ R) :
    PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem zero_iff {C R : Type*} [Category C] [Category R]
    [HasZeroMorphisms C] [HasZeroMorphisms R] (F : C ⥤ R)
    [F.Faithful] [F.PreservesZeroMorphisms] (X : C) : IsZero X ↔ IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
  constructor
  · intro h
    rw [← F.map_id, h, F.map_zero]
  · intro h
    apply F.zero_of_map_zero (𝟙 X)
    exact (F.map_id X).trans h

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]

variable (ell : ℕ) [Fact ell.Prime]


private lemma geometric_clause (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
      RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
          F.obj.carrier)) :
    functorGeometricCompatibility D U₀ t G ell A S e.functor β hL →
      geometricCompatibility D U₀ t G ell A S e β hL := by
  unfold geometricCompatibility functorGeometricCompatibility
  exact fun h ↦ h

private lemma return_clause (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
      RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
          F.obj.carrier)) :
    functorReturnCompatibility D U₀ t G ell A S e.functor β hL →
      returnCompatibility D U₀ t G ell A S e β hL := by
  unfold returnCompatibility functorReturnCompatibility
  exact fun h ↦ h

private lemma tensor_clause (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A) :
    functorTensorCompatibility D U₀ t G ell A e.functor →
      tensorCompatibility D U₀ t G ell A e := by
  unfold tensorCompatibility functorTensorCompatibility
  exact fun h ↦ h

private lemma tensor_fibre_clause (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hT : ∀ F H : Lisse ell (D.geometricFrobenius U₀),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
        (pairTensor ell (D.geometricFrobenius U₀) F H).carrier) :
    functorTensorFibreCompatibility D U₀ t G ell A e.functor β hT →
      tensorFibreCompatibility D U₀ t G ell A e β hT := by
  unfold tensorFibreCompatibility functorTensorFibreCompatibility
  exact fun h ↦ h


set_option maxHeartbeats 4000000 in
-- The normalized comparison clauses elaborate several dependent categorical interfaces.
/-- Exactness, abelianness and zero detection follow from descent, rather than being
additional descent assumptions.

Source: Weil II (1.1.12), steps 8--9 of the generic-fibre proof.
(blueprint: lem-dl-a1-normalized-weil-assertions).

Proof: coefficient-heart closure makes the source abelian and its forgetful functor exact.
Transfer finite products and the abelian structure across the equivalence obtained from full
faithfulness and essential surjectivity. Both equivalence functors preserve limits and colimits.
The normalized comparison clauses retain their original terms, since the forward functor is
unchanged. For zero detection, map the identity through the two faithful functors and use the
criterion that a representation is zero exactly when its vector space is subsingleton. -/
theorem normalized_functor_assertions
    [TopologicalSpace.NoetherianSpace (D.geometricFiber U₀).left]
    (A : Geometry D U₀ t G) (S : RealCondensedFibre.System.{u} ell)
    (M : NormalizedFunctor D U₀ t G ell A S)
    [M.functor.Full] [M.functor.Faithful] [M.functor.EssSurj] :
    Nonempty (Assertions D U₀ t G ell A S) := by
  have : M.functor.IsEquivalence := {}
  let e := M.functor.asEquivalence
  obtain ⟨⟨hAb⟩, hlim, hcolim⟩ :=
    lisse_weil_abelian ell (D.geometricFrobenius U₀)
      ⟨pairUnit ell (D.geometricFrobenius U₀), M.unit_lisse⟩
  let := hAb
  obtain ⟨hRAb⟩ := abelian_target e
  let := hRAb
  obtain ⟨hl, hc, hil, hic⟩ := equivalence_exact e
  let J := e.functor ⋙ (ObjectProperty.ι _)
  have : J.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full J
  refine ⟨{
    equivalence := e
    comparison := M.comparison
    linear := M.linear
    restriction_lisse := M.restriction_lisse
    geometric_action := ?_
    return_action := ?_
    sourceAbelian := ⟨hAb⟩
    targetAbelian := ⟨inferInstance⟩
    exact := ⟨hl, hc⟩
    inverse_exact := ⟨hil, hic⟩
    forget_exact := ⟨hlim, hcolim⟩
    tensor := ?_
    tensor_lisse := M.tensor_lisse
    unit_lisse := M.unit_lisse
    unit_trivial := M.unit_trivial
    tensor_comparison := ?_
    subobjects := ?_
    zero := ?_ }⟩
  · exact geometric_clause D U₀ t G ell A S e M.comparison M.restriction_lisse
      M.geometric_action
  · exact return_clause D U₀ t G ell A S e M.comparison M.restriction_lisse M.return_action
  · exact tensor_clause D U₀ t G ell A e M.tensor
  · exact tensor_fibre_clause D U₀ t G ell A e M.comparison M.tensor_lisse M.tensor_comparison
  · exact equivalence_subobjects D U₀ t G ell A e
  · intro F
    exact (zero_iff J F).trans
      (Rep.isZero_iff (CondensedLisseMonodromy.Coeff ell) (Group D U₀ t G)
        (e.functor.obj F).obj)

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
