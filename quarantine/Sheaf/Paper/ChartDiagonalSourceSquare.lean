/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.GeneralChartComparisons

/-! # Naturality of the diagonal source factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The diagonal source counit square for an arbitrary etale map of affine charts.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Step 3
(blueprint: lem-pur-chart-diagonal-source-square).

Proof: factor the map of self-products through the pullback of the target's first
projection. Near the diagonal its first factor is etale and the centre is Cartesian;
remove the closed off-diagonal component to obtain this neighbourhood. Source-etale
restriction followed by inverse smooth base change is precisely sourceOrdinary.
Source-etale/base-change interchange for the dualizing sigma cocycle and vertical
pasting identify its composite with the inverse of each self-product base-change
mate. Pull back along the source diagonal. Its two projection composites are the
identity, so the pullback composition constraints give finiteDiagonalRestriction.
Transport along sourceComparison, diagonalDualizingComparison and pullComparison;
these constraints cancel on both routes and give the displayed square. This uses
only the specified counit mates and applies also in dimension zero and on empty
schemes; neither a coordinate-compatible map nor an orientation is assumed. -/
theorem chart_diagonal_source_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    q P aV e N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (alpha P aV B) = alpha P aV C ≪≫ eps P aV e N := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartComparisons
