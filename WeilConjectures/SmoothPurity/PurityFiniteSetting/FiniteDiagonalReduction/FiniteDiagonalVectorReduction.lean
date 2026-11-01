/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteBundleSectionAdjointScalar
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalPresentationTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalRootComparison

/-! # Coefficient reduction of the normal-bundle vector factor

(blueprint: lem-pur-finite-diagonal-vector-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 3--4;
parent node proof Step 8.
Proof: `N = ℓ^n` is invertible on the k-scheme `X`, so the root comparison
`finiteDiagonalRootComparison` gives normalized coefficient-line data `e`. The
finite bundle-section scalar square `finiteBundleSectionAdjoint_scalar`, applied to
the diagonal conormal bundle at exponents `N` and `M = ℓ^m`, gives the ordinary
equation, and `finiteDiagonalPresentationTransport` transports it through the
pro-etale presentations to the displayed square, including rank zero and arbitrary
ramification; quotient flatness is never used.
(blueprint: lem-pur-finite-diagonal-vector-reduction). -/
theorem diagonalVectorReduction :
    ∃ e : CoefficientLineComparison (quotient P m hm hmn)
        P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
        P.diagonalExponent_annihilates
        (P.finiteReductionSetting m hm).diagonalExponent_annihilates X,
      (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d e =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom := by
  let Q := P.finiteReductionSetting m hm
  letI := P.noetherian (f ≫ aY)
  letI := (chartDiagonalNormalBundle d f).1
  obtain ⟨e⟩ := finiteDiagonalRootComparison P m hm hmn (P.diagonalExponent_isUnit (f ≫ aY))
  refine ⟨e, ?_⟩
  have hN : 0 < P.diagonalExponent := by
    dsimp only [PurityFiniteSetting.diagonalExponent]
    exact pow_pos P.coefficients.prime.out.pos P.level
  have hM : 0 < Q.diagonalExponent := by
    dsimp only [Q, PurityFiniteSetting.diagonalExponent]
    exact pow_pos Q.coefficients.prime.out.pos Q.level
  have hMN : Q.diagonalExponent ∣ P.diagonalExponent := by
    dsimp only [Q, PurityFiniteSetting.diagonalExponent]
    exact pow_dvd_pow P.coefficients.l hmn
  have hcore := finiteBundleSectionAdjoint_scalar
    (quotient P m hm hmn) P.diagonalExponent Q.diagonalExponent hN hM hMN
    P.diagonalExponent_annihilates Q.diagonalExponent_annihilates X d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)
    (P.diagonalExponent_isUnit (f ≫ aY))
    (Q.diagonalExponent_isUnit (f ≫ aY)) e
  exact (finiteDiagonalPresentationTransport P m hm hmn d f aY e) hcore

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
