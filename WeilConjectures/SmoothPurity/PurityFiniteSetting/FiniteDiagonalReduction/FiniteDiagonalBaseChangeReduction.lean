/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothDiagonalScalar

/-! # Coefficient reduction of the diagonal base-change factor

(blueprint: lem-route-diagonal-base-change-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

attribute [local implicit_reducible] Dnc.sourceEtale Dnc.sourceSection
  comparison ordinaryScalar proScalar Etale.dualizingComplex Etale.sectionInvariant

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

set_option linter.unusedSectionVars false in
/-- Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Step 3;
parent node proof Step 5.
Proof: the inverse smooth base-change map is the adjunction mate of the pullback
base-change square. Apply scalar extension to its unit-and-counit formula and use
scalar pullback balancing and reduced-counit compatibility. The same triangle
identities identify the two resulting mates. Pull along the diagonal, whose
composite with the first projection is the identity, and insert the coefficient-unit
and intrinsic realization comparisons. These are exactly omegaMap and
diagonalSectionMap, so the inverse-alpha square commutes. The argument uses no
orientation and works in relative dimension zero and for identity reductions.
(blueprint: lem-route-diagonal-base-change-reduction). -/
theorem diagonalBaseChangeReduction :
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalAlpha d f aY).inv ≫
        diagonalSectionMap P m hm hmn d f aY =
      omegaMap P m hm hmn f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalAlpha d f aY).inv := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  let := (P.comparedDiagonalBaseChange d f (f ≫ aY) aY rfl).2.2.2.1
  let := ((P.finiteReductionSetting m hm).comparedDiagonalBaseChange d f
    (f ≫ aY) aY rfl).2.2.2.1
  have hN : 0 < P.diagonalExponent := by
    exact pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level
  -- The same annihilator works after the coefficient quotient.
  have hB : ((P.diagonalExponent : ℕ) :
      (P.finiteReductionSetting m hm).Coefficient) = 0 := by
    rw [← map_natCast (quotient P m hm hmn), P.diagonalExponent_annihilates, map_zero]
  have h := finiteSmoothDiagonalScalar (quotient P m hm hmn)
    P.diagonalExponent hN P.diagonalExponent_annihilates hB
    (P.diagonalExponent_isUnit aY) f d
  -- The ordinary diagonal factor is the inverse of the chart restriction.
  have hh : (ordinaryScalar (quotient P m hm hmn) X).map
        (P.diagonalComparedRestriction f
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback f f).flip))).inv ≫
        DncCoefficientTransport.sectionMap (quotient P m hm hmn)
          (pullback.fst f f) (pullback.diagonal f) =
      DncCoefficientTransport.dualizingMap (quotient P m hm hmn) f ≫
        ((P.finiteReductionSetting m hm).diagonalComparedRestriction f
          (asIso (Etale.dualizingComplexBaseChangeMap
            (P.finiteReductionSetting m hm).Coefficient
            (IsPullback.of_hasPullback f f).flip))).inv := by
    with_unfolding_all exact h
  have ha := (ProEtale.pbcComparisonReduction X (quotient P m hm hmn)).hom.naturality
    (P.diagonalComparedRestriction f
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
        (IsPullback.of_hasPullback f f).flip))).inv
  have hu := (ProEtale.pbcComparisonReduction X (quotient P m hm hmn)).hom.naturality
    (P.chartDualizingUnit f).inv
  -- Transport through the fixed site comparison and cancel the presentations.
  unfold diagonalSectionMap omegaMap
  unfold presented realize
  unfold chartDiagonalAlpha
  dsimp only [Dnc.sourceComparison, Dnc.sourceEtale, Dnc.sourceSection, comparison]
  simp only [Functor.map_comp, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.map_inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]
  dsimp only [comparison, proScalar, ordinaryScalar, Etale.scalarExtension,
    Functor.comp_map] at ha hu ⊢
  erw [reassoc_of% ha, reassoc_of% hu]
  simp only [Iso.map_hom_inv_id_assoc]
  have hc := congrArg (comparison (P.finiteReductionSetting m hm).Coefficient X).map hh
  dsimp only [comparison, ordinaryScalar, Etale.scalarExtension] at hc
  simp only [Functor.map_comp] at hc
  erw [reassoc_of% hc]

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
