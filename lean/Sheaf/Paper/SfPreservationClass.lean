/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.PurityAffineChartBounds
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.ExceptionalAdjointAdmissibility
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.PurityFiniteSetting
/-!
# Uniform finite-stage exceptional inverse-image preservation

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
`thm-sf-preservation-class`, order 2085 (blueprint: thm-sf-preservation-class).

The functor is the constructible comparison-transported étale exceptional functor.
The conclusion gives the constructible analogues of preservation clauses (2) and (3)
of exceptional-adjoint admissibility. No unrestricted ambient adjoint or FullCD datum
is an input or an output. There is no assertion about integral or field coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Uniform cohomological and Tor bounds for the constructible exceptional inverse image.
The interval and Tor predicates are the published fixed-scalar module-sheaf
presentation, at the actual positive finite coefficient quotient. At these finite stages
bounded constructibility agrees with the intrinsic notion by the origin comparison.
The target dimension is zero for the empty scheme. The maximum includes empty source
charts and equals zero for an empty chart family.

Source: blueprint thm-sf-preservation-class, order 2085
(blueprint: thm-sf-preservation-class).

Proof:
1. Identify the functor with ν_X^* f^× Rν_{Y,*}, as in
   def-weil-exceptional-inverse-image. By lem-sf-proetale-constructible-origin every
   bounded constructible input, including every finite-Tor constructible input, is
   of étale origin. The adjunction of cor-sf-ambient-adjoint-discharge is relative
   to that class; no unrestricted ambient right adjoint is used.
2. Apply `sf_purity_affine_chart_bounds` (cor-pur-general-admissibility-datum)
   directly to the supplied C. Its interface accepts arbitrary chart families and
   forms `C.nonemptyCharts` internally. This concrete restriction keeps the target
   cover, reindexes exactly the nonempty source charts by `Fintype.equivFin`, and
   inherits their dimensions and closed presentations. Any covering chart containing
   a point survives, so the restricted family still covers; its source-nonemptiness
   follows from the index subtype. Its maximum D₀=`C.nonemptyCharts.maxDimension`
   is at most D=`C.maxDimension`: each restricted index selects an original index
   with the same dimension, bounded by the original finite supremum. Its constants are
   c_U=2(d_U+dim Y) and c₀=max_U(c_U+1+2(D₀-d_U)). It gives constructibility,
   finite-Tor membership, and both interval bounds [a-2D₀,b-2D₀+c₀].
3. Every summand in c₀ is 2D₀+2dim Y+1, so the upper endpoint is b+2dim Y+1.
   Since D₀≤D, widen the lower endpoint to a-2D. Vanishing outside an interval
   persists on widening, including after tensoring each degree-zero module sheaf.
   If X is empty, each object of its small pro-etale site has the empty covering;
   all module sheaves and hence all cohomology sheaves are zero. If Y is empty,
   X is empty too. These arguments apply even if empty charts inflate the supplied D.
   For an empty chart family D=0; for an empty target e=0, as stated.
4. Keep the same charts while varying every n≥1. None of d_U, D, or dim Y depends
   on n; the identical cancellation gives the same shifts at all finite stages.
   Thus the universal quantifier over n below uses one fixed C and the same bounds.
5. Read these as signed shifts c_f^-=-2D and c_f^+=2e+1 in preservation clauses
   (2) and (3). Finite-Tor membership is included explicitly. The stronger ambient
   clause (1), its unrestricted adjoint datum, and coefficient-comparison assertions
   at integral or field stages are neither assumed nor concluded. -/
theorem sf_preservation_class
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Y : Scheme.{u}) [X.Over (Spec (.of F.k))] [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))] [QuasiCompact (Y ↘ Spec (.of F.k))]
    [IsSeparated (Y ↘ Spec (.of F.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of F.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) (C : SfAffineChartPresentation f) :
    ∀ (n : ℕ) (hn : 1 ≤ n) (a b : ℤ) (_hab : a ≤ b),
      (∀ L : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          Y a b L →
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.maxDimension : ℤ)) (b + 2 * (sfDimension Y : ℤ) + 1)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj L)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y a b K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.maxDimension : ℤ)) (b + 2 * (sfDimension Y : ℤ) + 1)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
