/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection

/-! # Native integral refinement invertibility

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence paragraph.
(blueprint: lem-sf-integral-native-refinement-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

private theorem isIsoOfCompEqId
    {C : Type*} [Category C] {A B : C} (a : A ⟶ B) (r : B ⟶ A) [IsIso a]
    (h : a ≫ r = 𝟙 A) : IsIso r := by
  have : IsIso (a ≫ r) := h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left a r

set_option maxHeartbeats 800000 in
-- Native refinement normalization has large derived-category endpoint types.
private theorem nativeRefinementIsIsoOfFamily
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (τ : ∀ c₁ c₂ : Compactification f,
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂)
    (hn : ∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
      (h₂ : d.Refinement c₂) (M : BoundedConstructible (condensedRingObj Λ X)),
      (τ c₁ c₂).hom.app M ≫ (refinement Λ h₂).app M.obj =
        (refinement Λ h₁).app M.obj)
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (M' : BoundedConstructible (condensedRingObj Λ X)) :
    IsIso ((refinement Λ u).app M'.obj) := by
  have heq := hn c₁ c₂ c₁ (Compactification.Refinement.id c₁) u M'
  have hid := NatTrans.congr_app
    (refinement_id_comp Λ c₁ (Compactification.Refinement.id c₁)
      (Compactification.Refinement.id c₁)).1 M'.obj
  exact @isIsoOfCompEqId (D Λ Y) inferInstance
    ((F Λ c₁).obj M'.obj) ((F Λ c₂).obj M'.obj)
    ((τ c₁ c₂).hom.app M') ((refinement Λ u).app M'.obj)
    (NatIso.hom_app_isIso (τ c₁ c₂) M') (heq.trans hid)

set_option maxHeartbeats 800000 in
-- Native derived-category endpoint checking needs additional heartbeats.
/-- Native integral refinements are invertible on bounded constructible inputs.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence paragraph.
(blueprint: lem-sf-integral-native-refinement-is-iso).

Proof: obtain the comparison isomorphisms normalized on every common refinement from
compactification independence. Use the common refinement with legs `(id, u)`. The
normalization identifies the composite of the comparison component and the native
refinement component with the identity-refinement component. The latter is the identity,
so cancellation of the comparison isomorphism proves the refinement is an isomorphism.
-/
theorem integralNativeRefinementIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenIntegralCoefficient l E)))
    (S : Scheme.{u}) (hl : ∀ s : S, IsUnit (l : S.residueField s))
    {X Y Y' : Scheme.{u}} [X.Over S] [Y.Over S] [Y'.Over S]
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    [LocallyOfFiniteType (Y' ↘ S)] [QuasiCompact (Y' ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver S] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v]
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (M : BoundedConstructible (condensedRingObj Λ X)) :
    IsIso ((refinement Λ u).app M.obj) := by
  have h := exchangeProjection_compactification_independent Λ l E 1
    (by rfl) (Or.inr (Or.inl hcoeff)) S hl f v
  let τ := h.choose
  have hn := h.choose_spec.choose_spec.1
  exact nativeRefinementIsIsoOfFamily Λ τ hn c₁ c₂ u M

end WeilConjectures
