/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.FieldTheory.SeparablyGeneratedDifferentialsBasis
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Differentials of a separably generated field extension

Source: Stacks Project, Algebra, proof of Tag 031W and the dimension assertion in the proof of
Tag 00TV.
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- The differentials of a separating transcendence basis form a basis, and the dimension
of the differentials is the transcendence degree.
Source: Stacks Project, Algebra, proofs of Tags 031W and 00TV. -/
theorem exists_basis_differentials_of_separating_transcendenceBasis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsep : Algebra.IsSeparableExtension k K)
    {r : ℕ} (x : Fin r → K) (hx : IsTranscendenceBasis k x)
    (hxs : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    (∃ b : Module.Basis (Fin r) K (KaehlerDifferential k K),
      ∀ i : Fin r, b i = D k K (x i)) ∧
    FiniteDimensional K (KaehlerDifferential k K) ∧
    (Module.finrank K (KaehlerDifferential k K) : Cardinal.{v}) = Algebra.trdeg k K := by
  obtain ⟨b, hb⟩ := exists_basis_differentials_of_separating_transcendenceBasis_basis
    hfg hsep x hx hxs
  refine ⟨⟨b, hb⟩, Module.Finite.of_basis b, ?_⟩
  rw [Module.finrank_eq_card_basis b]
  have hcard := hx.lift_cardinalMk_eq_trdeg
  simpa using hcard

end KaehlerDifferential
