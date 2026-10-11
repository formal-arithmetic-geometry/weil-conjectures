/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Homology.ModuleCohomologyBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Affine perfect-complex cut in degree zero

Source: Stacks Project, More on Algebra, Tag 0A1U, Lemma better-cut-complex-in-two
(blueprint: lem-pc-affine-perfect-cut-degree-zero).
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

/-- A bounded-above finite free complex splits at zero after shrinking around a prime
where its degree-zero cohomology base-change map is surjective.
Source: Stacks Project, More on Algebra, Tag 0A1U
(blueprint: lem-pc-affine-perfect-cut-degree-zero).

Proof: In the residue-field degree-zero term choose bases of the boundary subspace, the
cohomology quotient, and the complement of the cycles. Lift boundary basis vectors from
`K⁻¹`, lift the cohomology basis to cycles using surjectivity, and lift the remaining basis
vectors from `K⁰`. Localize away from the prime so these form a basis of `K⁰` and the images
of the last vectors in `K¹` have finite projective cokernel, using
`lem-pc-finite-projective-cokernel-localization`. This cokernel is the degree-one term of
the positive truncation; all its higher terms are the original finite free modules.
Thus it is bounded finite projective in degrees `[1,b]`, hence perfect and has no tensor
cohomology below one. Finally apply `lem-pc-derived-splitting-unique` with `a = 1` to the
standard truncation triangle to obtain the direct-sum isomorphism. -/
theorem affine_perfect_cut_degree_zero {R : Type v} [CommRing R]
    [∀ f : R, HasDerivedCategory.{v} (ModuleCat.{v} (Localization.Away f))]
    (p : Ideal R) [p.IsPrime] (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ b : ℤ, K.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (K.X i) ∧ Module.Finite R (K.X i))
    (hsurj : Epi (ModuleCat.cohomologyBaseChange (B := p.ResidueField) K 0)) :
    ∃ f : R, f ∉ p ∧
      Nonempty (Q.obj ((RingTensorCohomology.extend R (Localization.Away f)).obj K) ≅
        Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncLE 0) ⊞
        Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1)) ∧
      (∃ (P : CochainComplex (ModuleCat.{v} (Localization.Away f)) ℤ) (b : ℤ),
        P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (Localization.Away f) (P.X i) ∧
          Module.Finite (Localization.Away f) (P.X i)) ∧
        Nonempty (Q.obj
          (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1) ≅
          Q.obj P)) ∧
      (Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1)).IsPerfect ∧
      ∀ N : ModuleCat.{v} (Localization.Away f),
        (Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1) ⊗
          (singleFunctor (ModuleCat.{v} (Localization.Away f)) 0).obj N).IsGE 1 := by
  sorry

end DerivedCategory
