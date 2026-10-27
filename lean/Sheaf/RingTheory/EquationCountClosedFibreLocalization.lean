/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.RingTheory.EquationCountLocalizePresentation
import WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Localization preserving a closed reduction and the expected equation count

Source: Stacks Project, Algebra, Tag 00ST, assertion (1)
(blueprint: lem-sfb-equation-count-closed-fibre-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- If the reduction of a polynomial presentation modulo `I` has the expected dimensions
on every nonempty fibre, some principal localization preserving that reduction is a relative
global complete intersection for the presentation obtained by adjoining an inverse variable.
The reduced equations present `S/IS` over `R/I`. The presentation predicate includes the
inequality on each nonempty fibre, so the difference of equation counts is signed.
Source: Stacks Project, Algebra, Tag 00ST, assertion (1)
(blueprint: lem-sfb-equation-count-closed-fibre-localization).

Proof:
1. If `S/IS` is zero, take `h = 0`, hence `g = 0`. Both the localization and the enlarged
   quotient are zero, and all fibre conditions are vacuous. Otherwise a maximal ideal of
   `S/IS` supplies a nonempty fibre, forcing `c ≤ m`.
2. At every prime of `S` containing `IS`, quotient-spectrum correspondence and the tensor
   pushout property identify its fibre over `R` with its fibre over `R/I`. Its dimension
   at that point is therefore at most `m-c`.
3. Apply lem-weil-pbc-fibre-dimension-bounded-open-upstairs at each such point, and take
   the union of the resulting opens. This gives an open `W` containing `V(IS)` where all
   local fibre dimensions are at most `m-c`.
4. Write the complement as `V(J)`. Disjointness from `V(IS)` gives `g ∈ J` congruent to
   one modulo `IS`, by lem-weil-pbc-spec-zero-loci-disjoint-unit-ideal. Then `D(g) ⊆ W`.
   Lift `g` to a polynomial `h`.
5. Localization base change identifies every fibre of `S_g` with a basic open in the
   original fibre. The fibre-prime bijection, invariance of dimension at a point on an
   open subspace, and lem-weil-pbc-dimension-supremum-local-dimensions bound its dimension
   above by `m-c`, including the empty case.
6. Use new-equation-count-localize-presentation to identify the enlarged quotient with
   `S_g`, with the displayed generator images. Presentation base change gives `m+1` variables
   and `c+1` equations in each fibre. The polynomial-quotient dimension lower bound gives
   dimension at least `(m+1)-(c+1) = m-c` on every nonzero fibre. Thus the enlarged
   presentation satisfies def-weil-pbc-relative-global-complete-intersection. -/
theorem exists_localization_relativeGlobalCompleteIntersection_preserving_reduction
    (R : Type u) [CommRing R] (I : Ideal R) (m c : ℕ)
    (f : Fin c → MvPolynomial (Fin m) R)
    (hdim : IsRelativeGlobalCompleteIntersectionPresentation
      (fun i ↦ MvPolynomial.map (Ideal.Quotient.mk I) (f i))) :
    ∃ h : MvPolynomial (Fin m) R,
      Ideal.Quotient.mk
          (I.map (algebraMap R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))))
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) = 1 ∧
      IsRelativeGlobalCompleteIntersectionPresentation
        (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (m + 1)) R)
          (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
          (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last m) - 1)) ∧
      ∃ e :
          (MvPolynomial (Fin (m + 1)) R ⧸
            Ideal.span (Set.range
              (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (m + 1)) R)
                (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
                (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last m) - 1)))) ≃ₐ[R]
          Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) h),
        (∀ i : Fin m,
          e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castSucc i))) =
            algebraMap (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
              (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) h))
              (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.last m))) =
          IsLocalization.Away.invSelf (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) := by
  sorry

end Algebra
