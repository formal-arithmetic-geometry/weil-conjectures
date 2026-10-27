/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.PodCompletionReindexCoherence

/-! # Identity and composition laws for a normalized tensor family

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL and 07A4
(blueprint: lem-pod-reindexing-tensor-family-identity-composition).

This is the identity/composition part of the fixed-family coherence argument. The
remaining tensor associator, braiding and unitor equations are isolated in the
companion tensor-constraints statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
Section-normalized identity and composition comparisons exist for every fixed family
of completion and tensor reindexings satisfying their component laws. The identity
comparison is induced by `MorphismProperty.Over.mapId` on sections. The compositor
is induced by `MorphismProperty.Over.mapComp`. Their coefficient maps agree after
each quotient projection, and the projections jointly detect completed sections;
therefore both are module isomorphisms. Localization gives the reduction and limit
equations, while the tensor generator formula gives the tensor equation. Naturality
and inverse laws follow from the site isomorphism identities. Empty sites and zero
objects are covered by the same formulas.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 03EL, 07A4 (blueprint: lem-pod-reindexing-tensor-family-identity-composition).
-/
theorem podReindexingTensorFamilyIdentityComposition
    (completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f)
    (tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex l E f (completion f))
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (completion f) (tensor f)) :
    ∃ identity : ∀ W : Scheme.{u}, isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _,
    ∃ composition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f], isoReductionIntegralInverse l E (h ≫ f) ≅
        isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h,
      let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
      A.Relabelling l E ∧ A.Identity l E ∧ A.Composition l E := by sorry

end WeilConjectures
