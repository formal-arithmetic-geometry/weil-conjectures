import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# An inclusion of finite simplicial sets is a chain of one-simplex extensions

Source: literature/stacks-project/simplicial.tex, Lemma 018S (blueprint:
lem-weil-pbc-simplicial-set-add-simplices)
-/

open CategoryTheory Simplicial Limits
open Opposite

universe u

namespace SSet

/-- An inclusion of finite simplicial sets can be built by adjoining one simplex
at a time. Source: literature/stacks-project/simplicial.tex, Lemma 018S, with
Lemma 018R (blueprint: lem-weil-pbc-simplicial-set-add-simplices).
The proof proceeds by induction on the finite set of nondegenerate simplices
of `V` outside `U`. Every simplex is an iterated degeneracy of a
nondegenerate one, so containing all such simplices forces equality. For the
induction step choose a missing nondegenerate simplex `x` of least degree
`n`; all lower-degree simplices already lie in `U`. Adjoin to `U` all
degeneracies of `x`. The surjection-injection factorization in the simplex
category and the simplicial identities show that this is a subcomplex, adds
nothing below `n`, adds exactly `x` in degree `n`, and adds only degenerate
simplices above `n`. It remains finite and nonempty in every degree, and has
one fewer missing nondegenerate simplex. Applying the induction hypothesis
and prepending this first extension gives the displayed chain. -/
theorem add_simplices
    (S : SSet.{u})
    (U V : S.Subcomplex)
    (hUV : U ≤ V)
    (hU_fin : ∀ (n : ℕ), Finite ((U : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hV_fin : ∀ (n : ℕ), Finite ((V : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hU_nonempty : ∀ (n : ℕ), Nonempty ((U : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hV_nonempty : ∀ (n : ℕ), Nonempty ((V : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    [SSet.Finite (U : SSet)] [SSet.Finite (V : SSet)] :
    ∃ (r : ℕ) (W : Fin (r + 1) → S.Subcomplex),
      W 0 = U ∧ W ⟨r, Nat.lt_succ_self r⟩ = V ∧
      (∀ (k : Fin r), W k.castSucc ≤ W k.succ) ∧
      (∀ (k : Fin r), ∃ (n : ℕ) (x : (W k.succ : SSet).obj
          (Opposite.op (SimplexCategory.mk n))),
        x.1 ∉ Set.range ((W k.castSucc).ι.app
          (Opposite.op (SimplexCategory.mk n))) ∧
        (∀ (i : ℕ), i < n →
          Set.range ((W k.succ).ι.app (Opposite.op (SimplexCategory.mk i))) =
            Set.range ((W k.castSucc).ι.app (Opposite.op (SimplexCategory.mk i)))) ∧
        Set.range ((W k.succ).ι.app (Opposite.op (SimplexCategory.mk n))) =
          Set.range ((W k.castSucc).ι.app (Opposite.op (SimplexCategory.mk n))) ∪ {x.1} ∧
        (∀ (j : ℕ) (z : (W k.succ : SSet).obj
            (Opposite.op (SimplexCategory.mk j))), n < j →
          z.1 ∉ Set.range ((W k.castSucc).ι.app
            (Opposite.op (SimplexCategory.mk j))) →
          z ∈ SSet.degenerate (W k.succ : SSet) j)) := by
  sorry

end SSet
