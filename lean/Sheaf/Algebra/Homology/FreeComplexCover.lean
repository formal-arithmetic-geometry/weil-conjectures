/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single

/-!
# A free two-term cover of a cochain complex

Source: Stacks Project, Differential Graded Algebra, Lemma 15.60.8 (Tag 09KN),
proof (blueprint: lem-pc-derived-free-complex-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-derived-free-complex-cover) Specialize the construction in
Stacks, Tag 09KN, to a ring with zero differential. For each element in every degree,
take a two-term free complex with differential the identity and map its generators
to that element and its differential. Add a one-term free complex for each cocycle.
These summands give degreewise and cocycle surjectivity. The upper generators and
the added cocycle summands form the left, zero-differential subcomplex; the lower
generators form the zero-differential quotient. Their underlying modules split in
each degree. -/
theorem exists_freeComplexCover {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ (S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
      (f : S.X₂ ⟶ M),
      (∀ n : ℤ, Function.Surjective (f.f n)) ∧
      (∀ (n : ℤ) (z : M.X n), M.d n (n + 1) z = 0 →
        ∃ x : S.X₂.X n, S.X₂.d n (n + 1) x = 0 ∧ f.f n x = z) ∧
      S.ShortExact ∧
      (∀ n : ℤ,
        Nonempty
          (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)).Splitting) ∧
      ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
        Nonempty (S.X₁ ≅ ∐ (fun i : I₁ =>
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
            (ModuleCat.of A A))) ∧
        Nonempty (S.X₃ ≅ ∐ (fun i : I₃ =>
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
            (ModuleCat.of A A))) := by
  sorry

end CochainComplex
