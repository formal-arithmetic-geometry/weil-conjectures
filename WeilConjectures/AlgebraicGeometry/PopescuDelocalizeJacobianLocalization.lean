/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.AlgebraicGeometry.PopescuAuxiliarySubmersivePresentation

/-!
# Standard smoothness of the dehomogenized Jacobian localization

## References

* Stacks Project, Tag 07F9, <https://stacks.math.columbia.edu/tag/07F9>
* Stacks Project, Tag 00T6, <https://stacks.math.columbia.edu/tag/00T6>
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

/-- The localization of the auxiliary quotient `R[x₀,x₁..,x_N,w]/(f)` at `x₀ * w * ∏ sⱼ`
is standard smooth over `R`, assuming the Jacobian minor condition `hs`
(Stacks, Tag 07F9 and Tag 00T6). -/
theorem popescu_auxiliary_isStandardSmooth
    (R : Type u) [CommRing R] (N c t : ℕ) (hc : c ≤ N)
    (f : Fin c → MvPolynomial (Fin N) R)
    (s : Fin (t + 1) → R) (h : MvPolynomial (Fin N) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f)) :
    Algebra.IsStandardSmooth R (Localization.Away (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun j : Fin c =>
        rename (fun i : Fin N => i.castSucc.succ) (f j))))
      (X (0 : Fin (N + 2)) * X (Fin.last (N + 1)) * C (∏ j : Fin (t + 1), s j)))) := by
  obtain ⟨P⟩ := popescu_auxiliary_submersivePresentation R N c t hc f s h hs
  exact P.isStandardSmooth

end Algebra
