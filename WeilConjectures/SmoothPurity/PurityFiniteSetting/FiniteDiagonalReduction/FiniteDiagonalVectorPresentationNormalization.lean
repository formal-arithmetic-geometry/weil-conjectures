/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartFactors.ChartDncVectorFactorData

/-! # Chart vector factor equals the canonical inverse integration presentation

Source: blueprint latest, smooth orientation charts and coefficient reduction.
(blueprint: lem-pur-finite-diagonal-vector-presentation-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The chart-defined vector factor is the inverse integration adjunct in the
canonical associated-graded bundle presentation.
Source: blueprint latest, smooth orientation charts proof, Step 4.
(blueprint: lem-pur-finite-diagonal-vector-presentation-normalization).

Proof: restrict to affine coordinate neighborhoods of the base and to a linear
frame of the conormal bundle. The cone model fixes its homogeneous generators,
projection and zero section. Source-etale orientation normalization identifies the
normal projection orientation with the inverse exceptional adjunct of the ordered
vector integration. Pull this equality to zero; the pullback compositor cancels
the bundle projection, and the canonical Tate pullback cancels its inverse.
The resulting formula is the inverse bundleSectionAdjoint following the canonical
normalBundleComparison. Both sides become maps of degree-zero Tate sheaves after
the common shift is removed. Sheaf Hom gluing gives the equality globally, including
non-affine bases, empty schemes and the rank-zero empty tensor. -/
theorem finiteDiagonalVectorPresentationNormalization :
    vectorFactor P d f aY =
      ChartFactors.beta P d f aY
        (Etale.canonicalEtaleCompactSupportNormalization P.Coefficient) := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
