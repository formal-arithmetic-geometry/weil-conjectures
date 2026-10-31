/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSourceChartPowerTransition

/-! # Independence of finite-reduction root coordinates

Source: blueprint finite reduction of purity, the root-line comparison in Step 1
(blueprint: lem-pur-finite-reduction-source-chart-independence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Conjugating any comparison of untwisted shifted objects by compatible root
charts is independent of the roots. The untwisted arrow is fixed, not constructed
by this assertion.

Source: blueprint `thm-pur-finite-reduction-of-purity`, Step 1, root-line and shift
comparison; Stacks 03PK and 07A4
(blueprint: lem-pur-finite-reduction-source-chart-independence).

Proof: any two primitive ell^n-th roots differ by raising to a power j coprime to
ell. Their ell^(n-m)-th powers differ by the same j. The section normalization of
finiteReductionRootTrivialization identifies the change of chart with multiplication
by j on the root line. The inverse chart therefore changes by j^(-1). Induct on
the ordered tensor power d: naturality of tensor reassociation and the tensor-unit
map shows that the source trivialization changes by j^(-d). Exact realization and
shift preserve this scalar action. Scalar extension sends the integer scalar j
and its inverse to the same scalars in the quotient. Every morphism of the derived
category of B-module sheaves commutes with these central scalar automorphisms.
Consequently the two chart-change factors on opposite sides of a cancel. For d=0
both factors are identities; empty schemes and the zero object obey the same
identities. No flatness of the quotient map or boundedness of K is used. -/
theorem finiteReductionSourceChart_independent (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (a : (P.finiteReduction m hm hmn X).obj
        (((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧) ≅
      (((P.finiteReductionSetting m hm).finiteReductionPullback f).obj
        ((P.finiteReduction m hm hmn Y).obj K))⟦2 * (d : ℤ)⟧)
    (ζ η ζ' η' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent)
    (hη' : IsPrimitiveRoot η' (P.finiteReductionSetting m hm).diagonalExponent)
    (h : η = ζ ^ (P.coefficients.l ^ (P.level - m)))
    (h' : η' = ζ' ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteReduction m hm hmn X).mapIso
        (P.finiteReductionSourceTrivialization f d ζ hζ K) ≪≫ a ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η hη
        ((P.finiteReduction m hm hmn Y).obj K)).symm =
    (P.finiteReduction m hm hmn X).mapIso
        (P.finiteReductionSourceTrivialization f d ζ' hζ' K) ≪≫ a ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η' hη'
        ((P.finiteReduction m hm hmn Y).obj K)).symm := by
  obtain ⟨c, -, hc⟩ := hζ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hηc : η = η' ^ c := by
    rw [h, h', ← hc, pow_right_comm]
  let F := P.finiteReduction m hm hmn X
  have : F.Additive := (P.finiteReductionAdjunction m hm hmn X).left_adjoint_additive
  let s := P.finiteReductionSourceTrivialization f d ζ hζ K
  let s' := P.finiteReductionSourceTrivialization f d ζ' hζ' K
  let t := (P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η hη
    ((P.finiteReduction m hm hmn Y).obj K)
  let t' := (P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η' hη'
    ((P.finiteReduction m hm hmn Y).obj K)
  have hs : s'.hom = c ^ d • s.hom :=
    P.finiteReductionSourceTrivialization_power d c ζ ζ' hζ hζ' hc.symm f K
  have ht : t'.hom = c ^ d • t.hom :=
    (P.finiteReductionSetting m hm).finiteReductionSourceTrivialization_power
      d c η η' hη hη' hηc f ((P.finiteReduction m hm hmn Y).obj K)
  change F.mapIso s ≪≫ a ≪≫ t.symm = F.mapIso s' ≪≫ a ≪≫ t'.symm
  apply Iso.ext
  apply (cancel_mono t'.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Functor.mapIso_hom]
  rw [ht, hs, Functor.map_nsmul]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.PurityFiniteSetting
