/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSourceChartPowerTransition

/-! # A uniform scalar for changes of finite purity source charts

Source: the root-chart calculation in def-pur-smooth-pullback-exchange.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Changing the primitive root rescales all source charts by the same integer.
Source: def-pur-smooth-pullback-exchange, middle identification and root-chart
normalization; def-pur-finite-reduction-root-charts, ordered tensor construction
(blueprint: lem-route-exists-finite-reduction-source-chart-scalar).

Proof: since zeta^N = 1 and eta is a primitive N-th root, there is a natural
number c with eta^c = zeta (IsPrimitiveRoot.eq_pow_of_pow_eq_one); c depends
only on zeta and eta. Put r = c^d. By finiteReductionSourceTrivialization_power
(lem-pur-finite-source-chart-power-transition) with old root zeta, new root eta
and zeta = eta^c, the hom of the source chart at eta is r times the hom of the
source chart at zeta, for every scheme, map and complex. Compose on the left
with the inverse zeta chart: composition distributes over natural-number
multiples (Preadditive.comp_nsmul) and inv ≫ hom is the identity, which gives
the displayed equality simultaneously for all schemes, maps and complexes.
-/
theorem exists_finiteReductionSourceChartScalar (P : PurityFiniteSetting.{u})
    (d : ℕ) (ζ η : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) :
    ∃ r : ℕ, ∀ {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
      (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring),
      (P.finiteReductionSourceTrivialization f d ζ hζ K).inv ≫
        (P.finiteReductionSourceTrivialization f d η hη K).hom =
          r • 𝟙 (((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧) := by
  obtain ⟨c, -, hc⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
  let r : ℕ := c ^ d
  refine ⟨r, ?_⟩
  intro X Y hX f K
  let s := P.finiteReductionSourceTrivialization f d ζ hζ K
  let t := P.finiteReductionSourceTrivialization f d η hη K
  have ht : t.hom = r • s.hom := by
    dsimp [t, s, r]
    exact P.finiteReductionSourceTrivialization_power d c ζ η hζ hη hc.symm f K
  change s.inv ≫ t.hom = r • 𝟙 (((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧)
  rw [ht]
  simp only [Preadditive.comp_nsmul, Iso.inv_hom_id]

end WeilConjectures.PurityFiniteSetting
