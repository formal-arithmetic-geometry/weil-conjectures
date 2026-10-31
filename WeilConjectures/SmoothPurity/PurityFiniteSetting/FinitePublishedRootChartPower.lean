/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootLinePowerTransition

/-! # Power equivariance of the published finite root charts

Source: finite-reduction-of-purity, Step 2, ordered powers of the root-line chart.
(blueprint: lem-pur-finite-published-root-chart-power).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem orderedPower_hom_nsmul {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [∀ M : C, (T.obj M).Additive]
    [∀ M : C, (T.flip.obj M).Additive]
    (B U : ℕ → C) (L V : C) (z : B 0 ≅ U 0) (t t' : L ≅ V)
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (a : ∀ n : ℕ, (T.obj (U n)).obj V ≅ U (n + 1))
    (c : ℕ) (ht : t'.hom = c • t.hom) (d : ℕ) :
    (finiteReductionOrderedPower T B U L V z t' s a d).hom =
      c ^ d • (finiteReductionOrderedPower T B U L V z t s a d).hom := by
  induction d with
  | zero => simp only [finiteReductionOrderedPower, pow_zero, one_nsmul]
  | succ d ih =>
    simp only [finiteReductionOrderedPower, compositionTensorMapIso,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    change (s d).hom ≫ ((T.flip.obj L).map _ ≫ _) ≫ (a d).hom = _
    rw [ih, ht, Functor.map_nsmul, Functor.map_nsmul]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, smul_smul, pow_succ, Nat.mul_comm]
    rfl

/-- Raising the root to a power rescales the inverse root chart by that power,
and rescales its ordered d-fold tensor by the d-th power of that scalar.

Source: `thm-pur-finite-reduction-of-purity`, proof Step 2, invertible-twist
compatibility; the ordered tensor construction in
`def-pur-finite-reduction-root-charts`.
(blueprint: lem-pur-finite-published-root-chart-power).

Proof: write N = ell^n. The section formula for the root trivialization sends a
constant coefficient b to b tensor the root. If zeta = eta^a, the trivialization
at zeta is a times the one at eta, because the roots group law is addition in
its associated Z/N-module. Compose with their inverse isomorphisms to get that
the inverse chart at eta is a times that at zeta. The single-complex functor and
the degree-two shift are additive, so the shifted degree-one charts obey the
same equation. Induct on d in finiteReductionOrderedPower. The zero chart is
independent of the root and a^0 = 1. At a successor, bilinearity of the derived
tensor changes the scalar a^d to a^d * a = a^(d+1); all reassociation, shift
and unit maps are fixed. Exact comparison pullback is additive. Composing with
its fixed shift comparison therefore preserves the equation and gives the
stated pro-etale chart. Empty schemes obey the same equations. Both roots are
primitive, so every root trivialization used in the argument is invertible. -/
theorem finiteReductionPowerTrivialization_pow (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d a : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) (h : ζ = η ^ a) :
    (P.finiteReductionPowerTrivialization T η hη d).hom =
      a ^ d • (P.finiteReductionPowerTrivialization T ζ hζ d).hom := by
  have hline : (P.finiteReductionShiftedLineChart T η hη).hom =
      a • (P.finiteReductionShiftedLineChart T ζ hζ).hom := by
    simp only [finiteReductionShiftedLineChart, Functor.mapIso_hom, Iso.symm_hom]
    rw [P.finiteReductionRootTrivialization_inv_power T a ζ η hζ hη h,
      Functor.map_nsmul, Functor.map_nsmul]
  have hetale : (P.finiteReductionEtalePowerTrivialization T η hη d).hom =
      a ^ d • (P.finiteReductionEtalePowerTrivialization T ζ hζ d).hom := by
    unfold finiteReductionEtalePowerTrivialization finiteReductionEtaleRootPowerChart
      finiteReductionEtalePowerAssembly
    exact orderedPower_hom_nsmul _ _ _ _ _ _ _ _ _ _ a hline d
  simp only [finiteReductionPowerTrivialization, Iso.trans_hom, Functor.mapIso_hom]
  rw [hetale, Functor.map_nsmul, Preadditive.nsmul_comp]

end WeilConjectures.PurityFiniteSetting
