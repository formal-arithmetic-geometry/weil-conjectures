/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootLinePowerTransition

/-! # Scalar compatibility of changes of primitive-root line charts

Source: finite reduction of purity, the root-line comparison in Steps 2--3
(blueprint: lem-pur-finite-reduction-line-chart-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The transported degree-one root chart on any k-scheme, with its canonical
shift isomorphisms. This is the same ordinary root chart used for the affine input.
Source: blueprint finite-reduction Step 2; Stacks 03PK
(blueprint: lem-pur-finite-reduction-line-chart-scalars). -/
def finiteReductionLineChart (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)) ≅
      (P.coefficientUnit T)⟦(2 : ℤ)⟧ :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring T
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
  let E := (Scheme.sfIntrinsicModuleEquivalence T P.Ring).functor.mapDerivedCategory
  E.mapIso (F.mapIso (P.finiteReductionShiftedLineChart T ζ hζ) ≪≫
    (F.commShiftIso (2 : ℤ)).app (Etale.ordinaryFiniteUnit P.Coefficient T)) ≪≫
    (E.commShiftIso (2 : ℤ)).app (F.obj (Etale.ordinaryFiniteUnit P.Coefficient T))

set_option backward.isDefEq.respectTransparency false in
private theorem lineChart_hom_power (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c) :
    (P.finiteReductionLineChart T ζ' hζ').hom =
      c • (P.finiteReductionLineChart T ζ hζ).hom := by
  have hline : (P.finiteReductionShiftedLineChart T ζ' hζ').hom =
      c • (P.finiteReductionShiftedLineChart T ζ hζ).hom := by
    simp only [finiteReductionShiftedLineChart, Functor.mapIso_hom, Iso.symm_hom]
    rw [P.finiteReductionRootTrivialization_inv_power T c ζ ζ' hζ hζ' hc,
      Functor.map_nsmul, Functor.map_nsmul]
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring T
  simp only [finiteReductionLineChart, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [hline, Functor.map_nsmul, Preadditive.nsmul_comp, Functor.map_nsmul,
    Preadditive.nsmul_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Changes of compatible primitive-root charts commute with any morphism between
reduced shifted coefficient units.

Source: blueprint `thm-pur-finite-reduction-of-purity`, Step 2 (invertible twist
compatibility) and Step 3 (reduction of the Kummer line); Stacks 03PK
(blueprint: lem-pur-finite-reduction-line-chart-scalars).

Proof: two primitive ell^n-th roots differ by raising to a power j coprime to ell.
Their compatible ell^m-th roots differ by the same power. The section formula for
finiteReductionRootTrivialization identifies the change of inverse root chart
with multiplication by j inverse. The two exact derived functors and their shift
comparisons preserve this integer scalar automorphism. Scalar extension sends
multiplication by j to multiplication by its image in the smaller quotient, and
preserves its inverse. Every morphism between modules commutes with integer
multiplication, hence also with these inverses. This is the displayed equation.
The argument applies to the identity reduction m=n, to ramified levels, and to
the empty scheme; it uses neither flatness of the quotient nor finite type of T. -/
theorem finiteReductionLineChart_scalars (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (a : (P.finiteReduction m hm hmn T).obj ((P.coefficientUnit T)⟦(2 : ℤ)⟧) ⟶
      ((P.finiteReductionSetting m hm).coefficientUnit T)⟦(2 : ℤ)⟧)
    (ζ η ζ' η' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent)
    (hη' : IsPrimitiveRoot η' (P.finiteReductionSetting m hm).diagonalExponent)
    (h : η = ζ ^ (P.coefficients.l ^ (P.level - m)))
    (h' : η' = ζ' ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteReduction m hm hmn T).map
        ((P.finiteReductionLineChart T ζ hζ).inv ≫
          (P.finiteReductionLineChart T ζ' hζ').hom) ≫ a =
      a ≫ ((P.finiteReductionSetting m hm).finiteReductionLineChart T η hη).inv ≫
        ((P.finiteReductionSetting m hm).finiteReductionLineChart T η' hη').hom := by
  obtain ⟨c, -, hc⟩ := hζ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hηc : η = η' ^ c := by
    rw [h, h', ← hc, pow_right_comm]
  let F := P.finiteReduction m hm hmn T
  have : F.Additive := (P.finiteReductionAdjunction m hm hmn T).left_adjoint_additive
  have hs := lineChart_hom_power P T c ζ ζ' hζ hζ' hc.symm
  have ht := lineChart_hom_power (P.finiteReductionSetting m hm) T c η η' hη hη' hηc
  change F.map (_ ≫ _) ≫ a = _
  rw [hs, ht]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Iso.inv_hom_id,
    Functor.map_nsmul, Category.comp_id]
  rw [F.map_id]
  simp only [Category.id_comp]

end WeilConjectures.PurityFiniteSetting
