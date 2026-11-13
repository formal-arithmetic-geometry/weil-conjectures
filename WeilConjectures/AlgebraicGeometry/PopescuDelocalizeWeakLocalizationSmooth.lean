/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.PopescuDelocalizeJacobianLocalization
import WeilConjectures.AlgebraicGeometry.PopescuDelocalizeDehomogenizationEquiv
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness of the localized auxiliary algebra in weak delocalization

## References

* Stacks Project, Tag 07F9, <https://stacks.math.columbia.edu/tag/07F9>
* Stacks Project, Tag 00T6, <https://stacks.math.columbia.edu/tag/00T6>
-/

@[expose] public section

universe u

open scoped BigOperators
open MvPolynomial

namespace Algebra

open Classical in
/-- The localized auxiliary algebra `B_b` constructed from the homogenized relations
is smooth over `R` (Stacks, Tag 07F9, Tag 00T6 and Tag 00T7).

The small polynomial ring numbers `x₁..,xₙ₊ₘ` by `Fin (n+m)` starting at zero.
In the large ring, index zero is `x₀`, index `i+1` is the original variable `i`,
and index `n+m+1` is the homogenizing variable. The sum in `hdegree` counts only
exponents of the last `m` original variables. The formula in `hF` homogenizes
those variables and leaves the first `n` variables as coefficient variables. -/
theorem popescu_delocalize_weak_localization_smooth
    (R : Type u) [CommRing R]
    (n m c t : ℕ) (hc : c ≤ n + m)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (g : Fin t → MvPolynomial (Fin n) R)
    (s : Fin (t + 1) → R)
    (h : MvPolynomial (Fin (n + m)) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f))
    (hg : ∀ j : Fin t,
      C (s j.succ) * rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈
        Ideal.span (Set.range f))
    (d : Fin c → ℕ)
    (hdegree : ∀ j : Fin c, ∀ e ∈ (f j).support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j)
    (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
    (hF : ∀ j : Fin c, F j =
      ∑ e ∈ (f j).support,
        C ((f j).coeff e) *
          (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
          X (Fin.last (n + m + 1)) ^
            (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) :
    Algebra.Smooth R (Localization.Away
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun j : Fin t =>
            rename (fun i : Fin n =>
              (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) ∪
            Set.range (fun j : Fin c => X (0 : Fin (n + m + 2)) * F j)))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
          C (∏ j : Fin (t + 1), s j)))) := by
  have := popescu_auxiliary_isStandardSmooth R (n + m) c t hc f s h hs
  obtain ⟨e⟩ := popescu_delocalize_dehomogenization_equiv_exists
    R n m c t f g s hg d hdegree F hF
  have := Algebra.IsStandardSmooth.of_algEquiv e.symm
  infer_instance

end Algebra
