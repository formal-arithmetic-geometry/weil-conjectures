/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# Right exactness in the top nonzero derived degree

Source: the long exact cohomology sequence, Milne, Lectures on Etale Cohomology,
Section 1; blueprint sk-prop-a1-kummer, Coefficients.
(blueprint: lem-pur-top-derived-right-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The top potentially nonzero right derived functor preserves finite colimits.
Source: Milne, Section 1, long exact cohomology sequence; blueprint sk-prop-a1-kummer,
Coefficients (blueprint: lem-pur-top-derived-right-exact).

Proof: the long exact sequence of a short exact sequence is exact at its degree-n
middle object. The next connecting morphism has zero target by the hypothesis,
so the map onto the degree-n last object is an epimorphism. The standard criterion
for finite-colimit preservation by additive functors between abelian categories
applies to these right-exact images of all short exact sequences. -/
theorem rightDerived_preservesFiniteColimits_of_succ_isZero
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [EnoughInjectives C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (n : ℕ)
    (h : ∀ M : C, IsZero ((F.rightDerived (n + 1)).obj M)) :
    PreservesFiniteColimits (F.rightDerived n) := by
  apply (preservesFiniteColimits_iff_forall_exact_map_and_epi (F.rightDerived n)).mpr
  intro S hS
  obtain ⟨δ, _, hδ⟩ := hS.exists_rightDerived_full_long_exact F
  obtain ⟨hex, w₁, _, h₁, _⟩ := hδ n
  refine ⟨hex, ?_⟩
  exact h₁.epi_f ((h S.X₁).eq_of_tgt (δ n) 0)

end CategoryTheory.Functor
