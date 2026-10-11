/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.CategoryTheory.BoundedSubobjectSize
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Bounded-size generators for acyclic complexes

Source: Stacks Project, `injectives.tex`, Lemma
`lemma-acyclic-quotient-complexes-bounded-size`
(blueprint: lem-pur-kinjective-acyclic-quotient-complexes-bounded-size).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- In a Grothendieck abelian category, there is one cardinal bounding the termwise
subobject size of bounded-above acyclic subcomplexes detecting every nonzero acyclic
complex, and of bounded-above acyclic complexes whose coproduct surjects onto any
acyclic complex. Size uses the same small subobject model as
`CategoryTheory.bounded_subobject_size_quotient_and_small_iso_classes`.

Source: Stacks Project, `injectives.tex`, Lemma
`lemma-acyclic-quotient-complexes-bounded-size`
(blueprint: lem-pur-kinjective-acyclic-quotient-complexes-bounded-size).

Proof:
1. Choose a generator `U` using `def-sp-grothendieck-abelian`. Put
   `c(λ) = |∐ λ copies of U|` and `κ = sup {c^n(|U|) | n ≥ 1}`.
2. Given `ψ : U ⟶ M.X n`, start with its image in degree `n`, the image of its
   differential in degree `n + 1`, and zero in higher degrees. Descending inductively,
   take the inverse image in degree `k - 1` of the kernel in degree `k`.
   Acyclicity (`def-pc-acyclic-complex-modules`) makes its map to that kernel epi.
   Apply `lem-pur-kinjective-surjection-bounded-size` to choose a subobject surjecting
   onto the kernel with size at most `c` of the kernel's size. This preserves the
   differential, makes the subcomplex exact at `k`, and bounds its terms by the
   iterates of `c`. Induction gives a bounded-above acyclic subcomplex through which
   `ψ` factors, with every term of size at most `κ`.
3. If `M` is nonzero, the generator supplies such a `ψ` with nonzero image in some
   degree, so the resulting subcomplex is nonzero, proving (1).
4. Perform step 2 for every map from `U` to every term of `M`. These maps jointly
   generate each term, so the coproduct of the resulting subcomplexes maps
   epimorphically to `M`, proving (2). Complexes and their morphisms are those of
   `def-pc-cochain-complex-modules`, with this abelian category in place of modules. -/
theorem exists_cardinal_acyclic_subcomplex_and_coproduct_quotient
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C] :
    ∃ κ : Cardinal.{v}, ∀ M : CochainComplex C ℤ, M.Acyclic →
      (¬ IsZero M → ∃ (N : CochainComplex C ℤ) (ι : N ⟶ M),
        Mono ι ∧ ¬ IsZero N ∧ (∃ b : ℤ, N.IsStrictlyLE b) ∧ N.Acyclic ∧
          ∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject (N.X n))) ≤ κ) ∧
      (∃ (I : Type v) (F : I → CochainComplex C ℤ) (π : ∐ F ⟶ M),
        Epi π ∧ ∀ i : I, (∃ b : ℤ, (F i).IsStrictlyLE b) ∧ (F i).Acyclic ∧
          ∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject ((F i).X n))) ≤ κ) := by
  sorry

end CochainComplex
