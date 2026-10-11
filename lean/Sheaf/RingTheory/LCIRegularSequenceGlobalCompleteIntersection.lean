/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.RingTheory.CompleteIntersectionOverField

/-!
# Local regular sequences give global complete intersections

Source: literature/stacks-project/algebra.tex, Algebra, Lemma 00SC
(blueprint: lem-weil-pbc-lci-regular-sequence-global-complete-intersection).
-/

universe u

namespace Algebra

/-- (blueprint: lem-weil-pbc-lci-regular-sequence-global-complete-intersection)
Let `P = k[x₁, ..., xₙ]`, `S = P/I`, and let `q` be a prime of `S`.
If the extension of `I` to `P` localized at the inverse image of `q` is generated
by a regular sequence, then some principal localization of `S` is a global
complete intersection over `k`. This is Lemma 00SC of the Stacks Project,
implication (5) => (1). Proof outline (following the node proof steps): localize
at the inverse image prime and identify the quotient with `S_q`; dimension theory
for a regular sequence gives `e = ht(q') - ht(q)` and local dimension `n - e`.
Clear denominators to obtain generators in `I`, then choose elements away from
the prime so that one principal open has dimension `n - e`. Adjoining an inverse
variable presents that localization as a quotient of a polynomial ring in `n + 1`
variables by `e + 1` equations; its dimension is `(n + 1) - (e + 1)`, so the
definition of global complete intersection applies. (blueprint:
lem-weil-pbc-lci-regular-sequence-global-complete-intersection)
-/
theorem exists_globalCompleteIntersection_of_regularSequence
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) (hq : q.IsPrime)
    (e : ℕ) (h : Fin e → Localization.AtPrime (q.comap
      (Ideal.Quotient.mk I)))
    (hreg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) (List.ofFn h))
    (hgen : Ideal.map
      (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) I =
      Ideal.span (Set.range h)) :
    ∃ g : (MvPolynomial (Fin n) k ⧸ I),
      g ∉ q ∧ Algebra.IsGlobalCompleteIntersection k
        (Localization.Away g) := by
  sorry

end Algebra
