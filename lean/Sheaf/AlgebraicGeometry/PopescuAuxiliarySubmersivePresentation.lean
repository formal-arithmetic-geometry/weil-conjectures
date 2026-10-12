module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! Explicit submersive presentation for the Popescu Jacobian localization.

(blueprint: popescu-auxiliary-submersive-presentation)

The presentation is obtained by adjoining an inverse to the localization element and
using the original equations together with the inverse relation.  The selected Jacobian
minor is a unit by the ideal membership hypothesis, so the resulting presentation is
submersive.  This theorem records the explicit finite variable and relation types; its
proof is deferred to the algebraic Jacobian calculation.
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

/-- Explicit finite presentation for the localized quotient.
(blueprint: popescu-auxiliary-submersive-presentation)

Proof: adjoin an inverse to the localization element, retain the original equations,
and compute the selected Jacobian minor. The ideal membership hypothesis makes that
minor a unit, so the resulting presentation is submersive.
-/
theorem popescu_auxiliary_submersivePresentation
    (R : Type u) [CommRing R] (N c t : ℕ) (hc : c ≤ N)
    (f : Fin c → MvPolynomial (Fin N) R)
    (s : Fin (t + 1) → R) (h : MvPolynomial (Fin N) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f)) :
    Nonempty (SubmersivePresentation R (Localization.Away (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun j : Fin c =>
        rename (fun i : Fin N => i.castSucc.succ) (f j))))
      (X (0 : Fin (N + 2)) * X (Fin.last (N + 1)) * C (∏ j : Fin (t + 1), s j))))
      (Fin (N + 3)) (Fin (c + 1))) := by
  sorry

end Algebra
