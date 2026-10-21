/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.Paper.ConstructibleIntervals
public import Sheaf.Paper.PurityAffineChartCover
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Data.Finset.Lattice.Fold
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.EtaleOriginDerivedCategory
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExplicitExceptionalPreservation
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.SmoothExceptionalPreservation

/-!
# Chartwise preservation for the constructible exceptional inverse image

Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2078 (blueprint: thm-pur-general-admissibility).

The finite chart data include the actual closed presentations and their open complements.
Charts may be empty. Suprema in the natural numbers have value zero on the
empty family; consequently the empty-source case has D = c = 0.

## Main definitions and statements

- `Scheme.PurityAffineChartCover`: the finite affine covers and closed presentations.
- `PurityAffineChartCover.maxEmbeddingDimension` and `preservationConstant`: the maxima.
- `PurityFiniteSetting.general_admissibility`: the conditional two-clause preservation theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! The chart-cover structure and its maxima are defined in
`Sheaf.Paper.PurityAffineChartCover`; this file states the preservation theorem. -/

namespace WeilConjectures.PurityFiniteSetting

/-- Conditional preservation with exactly the chart maxima of the blueprint.
Source: blueprint order 2078 (blueprint: thm-pur-general-admissibility).

Proof, following the nine steps of the node:
1. Finite-type schemes over k are Noetherian and quasi-separated. Nagata compactifies f;
   the proper factor has finite dimension. Use thm-sf-ambient-adjoint-class and
   cor-sf-ambient-adjoint-discharge on the bounded-below etale-origin categories, with
   lem-sf-proetale-constructible-origin providing the witnesses. The compact-support
   comparison and the defining transport formula give the adjunction on these categories.
2. For each affine base open V, cor-exc-base-change-open-immersion-general identifies
   restriction of Rf! with Rf_V! after restriction to V. By prop-exc-open-adjoint and
   thm-exc-explicit-preservation, this input restriction preserves both intervals.
3. On a chart U, exact open restriction preserves etale origin. Compact-support composition
   and uniqueness of right adjoints identify the chart restriction of Rf! with Ri! Rpi!,
   using thm-sf-comp-composition and lem-cat-right-adjoint-composition.
4. The projection pi is separated and smooth of relative dimension d_U. Apply
   cor-pur-smooth-admissibility separately to constructible and finite-Tor inputs, obtaining
   the shift [a-2d_U,b-2d_U]. No finite-Tor hypothesis is used for the first clause.
5. Choose a bounded constructible etale representative of this chart input. Exact comparison
   and full faithfulness reflect cohomological bounds; lem-sf-comparison-tor-amplitude
   reflects the Tor bounds. The defining transport identifies Ri! with comparison applied
   to the ordinary etale closed adjoint.
6. The two open-complement clauses give vanishing above c_U and constructibility of every
   higher direct image of a constructible sheaf. Apply lem-exc-closed-amplitude and
   prop-exc-closed-tor, using lem-exc-closed-ambient. Their interval is
   [a-2d_U,b-2d_U+c_U+1]. Comparison preserves constructibility and both intervals.
7. Each d_U is at most D, and c is at least c_U+1+2(D-d_U). Thus each chart interval is
   contained in [a-2D,b-2D+c]. For no charts, X is empty and sheaves are zero by the
   empty-cover sheaf condition, so D=c=0 works.
8. Exact open restriction commutes with cohomology. The cover detects zero sheaves, and
   finite constructible stratifications glue by ordering the opens and intersecting the
   strata with U_i minus the earlier opens. This proves the first conclusion. Applying it
   to any cohomological interval of a bounded constructible object proves boundedness
   and constructibility for the finite-Tor input as well.
9. For every pro-etale module sheaf M, lem-pur-derived-pullback-tensor-iso identifies the
   restriction of Rf!K tensor M with the tensor of the restricted factors. By exactness,
   the chart Tor bound makes each outside cohomology sheaf vanish after restriction.
   The sheaf condition detects its vanishing globally. This proves Tor amplitude against
   all degree-zero pro-etale module sheaves, and hence finite-Tor constructible preservation.
-/
theorem general_admissibility (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Scheme.PurityAffineChartCover f)
    (cU : (v : Fin C.baseCount) → Fin (C.chartCount v) → ℕ)
    (hC : C.openComplementConditions P.Coefficient cU)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ K, Scheme.finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
      P.level_pos Y
      (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k))) a b hab K →
      Scheme.finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
        P.level_pos X (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)))
        (a - 2 * (C.maxEmbeddingDimension : ℤ))
        (b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ))
        (le_trans (sub_le_sub_right hab _)
          (le_add_of_nonneg_right (Nat.cast_nonneg _)))
        ((P.exceptionalInverseImage f).obj K)) ∧
    (∀ K, finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      Scheme.HasProEtaleTorAmplitude Y P.Ring K a b →
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
        ((P.exceptionalInverseImage f).obj K) ∧
      Scheme.HasProEtaleTorAmplitude X P.Ring ((P.exceptionalInverseImage f).obj K)
        (a - 2 * (C.maxEmbeddingDimension : ℤ))
        (b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ))) := by
  sorry

end WeilConjectures.PurityFiniteSetting
