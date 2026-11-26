/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Basis.SMul
import WeilConjectures.RingTheory.ZeroVariableConormalStabilization

/-!
# Stabilization for localized conormal bases

Auxiliary stabilization result for localized conormal bases: a stably free localized conormal
module becomes free with a basis of relation classes after adjoining variables sent to zero.

## References

* [Stacks, Tag 07EZ]
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

/-- Given a stable trivialization `(A_a ⊗ I/I²) × A_aʳ ≃ A_a^q` of the localized conormal module
of a presentation, adjoining `r` variables sent to zero yields a presentation with at least `q`
relations whose first `q` localized conormal classes form a basis.
No smoothness hypothesis or rank bound on the polynomial variables is used here. -/
theorem exists_stabilized_presentation_localized_conormal_basis
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    {n₀ m₀ : ℕ} (P₀ : Presentation R A (Fin n₀) (Fin m₀)) (r q : ℕ)
    (hstable : Nonempty
      (((Localization.Away a ⊗[A] P₀.toExtension.Cotangent) ×
        (Fin r → Localization.Away a)) ≃ₗ[Localization.Away a]
        (Fin q → Localization.Away a))) :
    ∃ (m : ℕ) (P : Presentation R A (Fin (n₀ + r)) (Fin m)) (hc : q ≤ m)
      (b : Module.Basis (Fin q) (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent)),
      ∀ j : Fin q, b j = 1 ⊗ₜ[A]
        (Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (Fin.castLE hc j),
            P.relation_mem_ker _⟩) := by
  classical
  obtain ⟨P₁, ⟨e⟩⟩ :=
    exists_zero_variable_presentation_localized_cotangent_equiv R A a P₀ r
  obtain ⟨e₀⟩ := hstable
  let b₀ := (Pi.basisFun (Localization.Away a) (Fin q)).map (e.trans e₀).symm
  let f := TensorProduct.mk A (Localization.Away a) P₁.toExtension.Cotangent 1
  have hlift (j : Fin q) : ∃ (g : P₁.toExtension.ker)
      (s : Submonoid.powers a), s • b₀ j = f (Extension.Cotangent.mk g) := by
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers a) f (b₀ j)
    obtain ⟨g, rfl⟩ := Extension.Cotangent.mk_surjective x
    exact ⟨g, s, hs⟩
  choose g s hs using hlift
  let w : Fin q → (Localization.Away a)ˣ := fun j =>
    (IsLocalization.map_units (Localization.Away a) (s j)).unit
  let b := b₀.unitsSMul w
  have hb (j : Fin q) : b j = 1 ⊗ₜ[A] Extension.Cotangent.mk (g j) := by
    rw [Module.Basis.unitsSMul_apply]
    change (↑(w j) : Localization.Away a) • b₀ j = f (Extension.Cotangent.mk (g j))
    simpa only [w, IsUnit.unit_spec, algebraMap_smul, Submonoid.smul_def] using hs j
  let rel : Fin (q + (m₀ + r)) → P₁.Ring :=
    Sum.elim (fun j => (g j).val) P₁.relation ∘ finSumFinEquiv.symm
  have hrel : Ideal.span (Set.range rel) = P₁.ker := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      dsimp only [rel, Function.comp_apply]
      cases finSumFinEquiv.symm i with
      | inl j => exact (g j).property
      | inr k => exact P₁.relation_mem_ker k
    · rw [← P₁.span_range_relation_eq_ker]
      apply Ideal.span_mono
      rintro x ⟨i, rfl⟩
      exact ⟨finSumFinEquiv (Sum.inr i), by simp [rel]⟩
  let P : Presentation R A (Fin (n₀ + r)) (Fin (q + (m₀ + r))) :=
    { toGenerators := P₁.toGenerators
      relation := rel
      span_range_relation_eq_ker := hrel }
  have hc : q ≤ q + (m₀ + r) := Nat.le_add_right _ _
  refine ⟨q + (m₀ + r), P, hc, b, ?_⟩
  intro j
  have hj : Fin.castLE hc j = Fin.castAdd (m₀ + r) j := rfl
  simpa only [P, hj, rel, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
    Sum.elim_inl] using hb j

end Algebra
