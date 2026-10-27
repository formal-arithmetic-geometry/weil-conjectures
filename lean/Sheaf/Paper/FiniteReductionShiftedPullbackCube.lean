/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.FiniteSmoothPullbackExchange

/-! # Finite scalar extension and the shifted ordinary pullback square

Source: blueprint finite-reduction-of-purity proof, Steps 2 and 4.
(blueprint: lem-pur-finite-reduction-shifted-pullback-cube)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Scalar extension respects the ordinary inverse-image square with an arbitrary shift.
There is no Tate line, root chart, smoothness assumption or exceptional inverse image.
Source: blueprint `thm-pur-finite-reduction-of-purity`, Steps 2 and 4;
Stacks 0D6D and 06YY
(blueprint: lem-pur-finite-reduction-shifted-pullback-cube).

Proof: compare the two composites of ordinary inverse images and exact restriction
of scalars. The section maps are the same pullback of a section with the same scalar
restriction; the two compositors are induced by the same fibre-product association.
Localizing this identity gives the derived restriction cube. Transpose its coefficient
edges through extension/restriction adjunctions. The triangle identities identify the
result with the coefficient/pullback comparisons in the statement. The section-unit
normalization of the raw pullback models identifies the geometric square with the
realization square used here. Exact restriction and inverse image commute termwise
with every integer shift. Scalar extension's shift is the adjoint of this exact shift,
so transposing the shifted restriction cube gives the displayed equation, including
its specified shift comparisons. Equivalently, first apply the unshifted cube and
then the shift compatibility of its coefficient mates. This uses derived extension,
not flatness of the quotient. Identity coefficient maps, empty schemes, zero objects
and shift zero satisfy the same formulas. -/
theorem finiteReduction_shiftedPullbackCube (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (r : ℤ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X').map
        (((P.finiteReductionPullback u).commShiftIso r).hom.app
          ((P.finiteReductionPullback f).obj K)) ≫
      (P.finiteReduction m hm hmn X').map
        ((P.finiteReductionPullbackSquare u f' f v sq K).hom⟦r⟧') ≫
      ((P.finiteReduction m hm hmn X').commShiftIso r).hom.app
        ((P.finiteReductionPullback f').obj ((P.finiteReductionPullback v).obj K)) ≫
      (P.finiteReductionPullbackComparison m hm hmn f'
        ((P.finiteReductionPullback v).obj K)).hom⟦r⟧' ≫
      (((P.finiteReductionSetting m hm).finiteReductionPullback f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom)⟦r⟧' =
    (P.finiteReductionPullbackComparison m hm hmn u
        (((P.finiteReductionPullback f).obj K)⟦r⟧)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (((P.finiteReduction m hm hmn X).commShiftIso r).hom.app
          ((P.finiteReductionPullback f).obj K) ≫
        (P.finiteReductionPullbackComparison m hm hmn f K).hom⟦r⟧') ≫
      (((P.finiteReductionSetting m hm).finiteReductionPullback u).commShiftIso r).hom.app
        (((P.finiteReductionSetting m hm).finiteReductionPullback f).obj
          ((P.finiteReduction m hm hmn Y).obj K)) ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullbackSquare u f' f v sq
        ((P.finiteReduction m hm hmn Y).obj K)).hom⟦r⟧' := by sorry

end WeilConjectures.PurityFiniteSetting
