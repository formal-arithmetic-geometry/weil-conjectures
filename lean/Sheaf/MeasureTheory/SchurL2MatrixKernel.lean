module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Schur bound for a measurable matrix integral kernel

Source: the agent-supplied analytic prerequisite for Demailly, `L² Hodge Theory`,
Part I §3.B, Theorem 3.6, printed p.13 (blueprint: lem-sfb-schur-l2-matrix-kernel).

The kernel values are continuous complex-linear maps between Euclidean spaces, hence carry
precisely the Euclidean operator norm. `NullMeasurable` expresses measurability for the
completion of product Lebesgue measure. Nonnegative extended integrals in the hypotheses
include finiteness, rather than using a real integral that vanishes when it diverges.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

/-- Schur's two-marginal estimate, including almost-everywhere absolute convergence and the
integral formula for every representative of each input class.

Source: the analytic prerequisite for Demailly, `L² Hodge Theory`, Part I §3.B,
Theorem 3.6, printed p.13 (blueprint: lem-sfb-schur-l2-matrix-kernel).

Proof plan:
1. Use `lem-sfb-measurable-parameter-bochner-integral` to replace completion-measurable
   functions by measurable representatives and obtain strongly measurable sections.
   Finite-dimensional Euclidean spaces, including rank zero, are separable Banach spaces.
2. Put k(x,y) = ‖G(x,y)‖ and v(y) = ‖f(y)‖. By
   `lem-sfb-tonelli-nonnegative-product`, the function U(x) = ∫ k(x,y)v(y)² dy is finite
   almost everywhere and its integral is at most b ‖h‖₂².
3. On the full-measure set where U and the row integral R are finite, apply
   `lem-sfb-real-l2-hilbert-pairing` to √k and √k v. This gives integrability of k v
   and the estimate ∫ k v ≤ √R √U ≤ √a √U, without division.
4. Apply `lem-sfb-vector-integral-majorant-linearity` and the operator-norm bound to
   G(x,y)(f(y)). The parameter integral is almost everywhere strongly measurable and has
   squared norm integral at most a b ‖h‖₂², so determines the required output class.
5. Two input representatives agree off a null set of y, for every fixed x; congruence of
   Bochner integrals gives the same output class.
6. Integral additivity and complex homogeneity give a complex-linear map. Taking square
   roots in step 4 proves its bound and hence continuity. No strict positivity of a, b,
   p or q was used. -/
theorem exists_schurL2MatrixKernel
    (m p q : ℕ) (hm : 1 ≤ m)
    (G : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hG : @NullMeasurable _ _ _
      (borel (EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q)))
      G (volume.prod volume))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ᵐ x ∂volume, ∫⁻ y, ‖G (x, y)‖ₑ ≤ ENNReal.ofReal a)
    (hcol : ∀ᵐ y ∂volume, ∫⁻ x, ‖G (x, y)‖ₑ ≤ ENNReal.ofReal b) :
    ∃ T : Lp (EuclideanSpace ℂ (Fin p)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin m))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ h : Lp (EuclideanSpace ℂ (Fin p)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin m))),
        ‖T h‖ ≤ Real.sqrt (a * b) * ‖h‖ ∧
        ∀ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℂ (Fin p),
          f =ᵐ[volume] h →
          (∀ᵐ x ∂volume, Integrable (fun y ↦ G (x, y) (f y)) volume) ∧
          (T h : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℂ (Fin q)) =ᵐ[volume]
            (fun x ↦ ∫ y, G (x, y) (f y)) := by
  sorry

end MeasureTheory
