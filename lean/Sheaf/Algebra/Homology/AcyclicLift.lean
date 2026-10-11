/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Lifting bounded-above acyclic complexes modulo an ideal

Source: Stacks Project, More on Algebra, Tag 0BC9, lemma-lift-acyclic-complex
(blueprint: lem-sc-complex-lift-acyclic-projective).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

/-- Stacks Project, Tag 0BC9 (blueprint: lem-sc-complex-lift-acyclic-projective).
Reduction modulo `I` is extension of scalars to `R ⧸ I`, canonically `P / IP`.
The direct-sum condition is stated for any module isomorphic to the binary direct sum,
as membership in a class of modules is understood up to isomorphism.

Proof: Choose an upper bound `b` and begin with the zero tail above `b`. Inductively split
an exact projective tail into terms `Zⁱ ⊕ Zⁱ⁺¹`; condition (2), applied from the top,
puts every cycle module in the class. Choose a projective lift of the next term of `E`.
Exactness identifies its differential's image with the reduction of the next cycle module.
Condition (1) lifts this map to that cycle module and condition (3) makes it surjective.
Append the resulting differential; its image equals the kernel of the next differential.
Repeat downwards. The tails agree, giving a bounded-above complex with terms in the class,
exact in each degree, and the reduction isomorphisms commute with every differential. -/
theorem exists_acyclic_lift_mod_ideal
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (hprojective : ∀ M, P M → Projective M)
    (hsummand : ∀ M₁ M₂ M₁₂ : ModuleCat.{max u v} R,
      P M₁ → P M₁₂ → Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂)) → P M₂)
    (hsurjective : ∀ (M₁ M₂ : ModuleCat.{max u v} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hbounded : ∃ b : ℤ, E.IsStrictlyLE b)
    (hacyclic : E.Acyclic)
    (hterms : ∀ i : ℤ, ∃ M : ModuleCat.{max u v} R, P M ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅ E.X i)) :
    ∃ A : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, A.IsStrictlyLE b) ∧ A.Acyclic ∧ (∀ i : ℤ, P (A.X i)) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A ≅ E) := by
  sorry

end CochainComplex
