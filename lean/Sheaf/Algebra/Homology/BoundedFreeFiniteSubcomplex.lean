/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Finite free subcomplexes of a bounded-above free complex

Source: Stacks Project, Tag 0FNR, `more-algebra.tex`,
`lemma-complex-bounded-above-free-colim-bounded-finite-free`
(blueprint: lem-zl-bounded-free-finite-subcomplex).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CochainComplex

/-- Every finite list of homogeneous elements of a bounded-above free complex lies in a
bounded subcomplex with finite free terms. The subcomplex is specified by its submodules
and their stability under the differential; its differentials are the restrictions of `F.d`.
Source: Stacks Project, Tag 0FNR,
`lemma-complex-bounded-above-free-colim-bounded-finite-free`.
(blueprint: lem-zl-bounded-free-finite-subcomplex).

Proof. For an empty list take the zero subcomplex. Otherwise choose a lower degree `a`
below all input degrees and at most `b + 1`, where `F` vanishes above `b`. Prove by descending
induction on `t`, from `b + 1` down to `a`, that every finite list in degrees at least `t`
lies in a finite free subcomplex supported in `[t, b]`. The base case is the zero complex.
For the induction step choose a basis of `F.X t` and the finite union `J` of the coordinate
supports of the inputs in degree `t`. Its coordinate submodule `E` is finite free, with
coordinates indexed by `J`. Choose a basis of `F.X (t + 1)` and the finite union `K` of the
supports of the differentials of these chosen basis elements. Apply the induction hypothesis
to the basis elements indexed by `K`, together with all original inputs in higher degrees,
obtaining `H`. Set `G` equal to zero below `t`, to `E` in degree `t`, and to `H` above `t`.
Differential stability below `t` follows from the zero domain, at `t` from the coordinate
expansions of the differentials in the span of `K`, and above `t` from stability of `H`.
The restricted differentials square to zero by the cochain identity of
`def-weil-abstract-derived-category`. All inputs belong to `G`; its terms are finite free
and vanish outside `[t, b]`. The finitely many induction steps give the result. Enumerating
each finite coordinate set identifies its module with `Fin r → A` for its cardinality `r`.
-/
theorem exists_bounded_finite_free_subcomplex
    {A : Type u} [CommRing A] (F : CochainComplex (ModuleCat.{v} A) ℤ)
    (hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → Subsingleton (F.X n))
    (hfree : ∀ n : ℤ, Module.Free A (F.X n))
    (xs : List (Σ n : ℤ, F.X n)) :
    ∃ G : (n : ℤ) → Submodule A (F.X n),
      (∀ p ∈ xs, p.2 ∈ G p.1) ∧
      (∀ n : ℤ, (G n).map (F.d n (n + 1)).hom ≤ G (n + 1)) ∧
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → G n = ⊥) ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty ((G n) ≃ₗ[A] (Fin r → A))) := by
  sorry

end CochainComplex
