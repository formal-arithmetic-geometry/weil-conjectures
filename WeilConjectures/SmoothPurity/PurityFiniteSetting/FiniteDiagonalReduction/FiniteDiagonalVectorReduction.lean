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

/-- The native shifted rank-`d` Tate-line reduction `rho` of the node, at the line level:
the generator-normalized comparison of the actual finite root lines for the quotient
`A_{E,n} → A_{E,m}`, sending `(a e_n) ⊗ b` to `ā b e_m` with `ζ_m = ζ_n^(N/M)`.
The normalizations (`roots_power`, `generators`, `derived_normalization`) pin every field,
so the selected comparison is the unique one of the positive-line comparison; existence is
`finiteDiagonalRootComparison`, using invertibility of the exponent on `X` from `f ≫ aY`.
Source: latest blueprint, `thm-pur-finite-reduction-of-purity.proof.md`, Step 2
(invertible twists); node proof Step 4
(blueprint: lem-route-diagonal-vector-reduction). -/
noncomputable def nativeCoefficientLineComparison :
    CoefficientLineComparison (quotient P m hm hmn)
      P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
      P.diagonalExponent_annihilates
      (P.finiteReductionSetting m hm).diagonalExponent_annihilates X :=
  Classical.choice (finiteDiagonalRootComparison P m hm hmn
    (P.diagonalExponent_isUnit (f ≫ aY)))

/--
The native finite coefficient reduction square for the diagonal normal-vector factor.
The comparison is the root-normalized finite Tate-line reduction supplied by the finite
coefficient setting; `normalSectionMap` is the transported normal-section map and
`vectorFactor` is the chart diagonal beta with its prescribed root transport. Thus the
morphism is the concrete pro-etale presentation of the derived square in the node
statement.

Proof (postponed), following the cited blueprint proof. The smooth separated diagonal is
regular of codimension `d`, so its associated graded normal cone with zero section is the
rank-`d` vector bundle used by `normalSectionMap`. The finite-type hypotheses supply the
Noetherian geometry needed for the ordinary coefficient square. On the ordinary etale
site, apply finite coefficient reduction to the integration-normalized bundle adjunct;
pull it to the zero section and use scalar and pullback balancing. This gives the square
for the ordinary section coefficient map. The site-comparison theorem transports that
square to the actual pro-etale normal section and identifies the transported inverse
adjunct with `vectorFactor`, independently of the annihilating root exponent. The
root-normalized positive-line comparison identifies the transported Tate-line arrow
with `nativeCoefficientLineComparison`; its tensor powers and shift are the prescribed
ones. Expanding the definitions of `normalSectionMap` and `vectorFactor`, naturality of
the scalar/site comparison rewrites both composites to the same arrow. The unit cases
`m = P.level` and `d = 0` use the scalar unit and empty tensor, and the empty scheme has
its unique maps. All coefficient extensions are derived, so no flatness or ramification
hypothesis is used.

Source: latest blueprint, `thm-pur-finite-reduction-of-purity.proof.md`, Steps 1--3;
(blueprint: lem-route-diagonal-vector-reduction).
-/
theorem diagonalVectorReductionNative :
    (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d (nativeCoefficientLineComparison P m hm hmn f aY) =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom := by
  sorry

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
