/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeExteriorDefs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement

/-! # Selected exterior summands and their determinant factors

Source: sk-p-real-purity, semisimplification, exterior summand and real dual
paragraphs (blueprint: lem-rp-native-exterior-certificates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Purely algebraic exterior certificates for a constituent and its contragredient.
Source: sk-p-real-purity, first through fifth proof paragraphs
(blueprint: lem-rp-native-exterior-certificates).

Proof: take an actual lisse composition series and its semisimplification. Exact
fibres preserve the local characteristic polynomials, hence reality. Group simple
summands by determinant weight gamma_1 > ... > gamma_t, of ranks r_j. For a factor
in block i put N=sum_{j<i} r_j and B=sum_{j<i} r_j gamma_j. The exterior weight formula
puts every simple constituent of wedge^(N+1) below B+gamma_i. This exterior power is
real. Its direct-sum decomposition contains the nonzero summand
(tensor_{j<i} det G_j) tensor G_i. For an eigenvalue alpha of the selected simple
factor, spectral functoriality gives an eigenvalue delta on this summand and on the
exterior power. Rank-one determinant purity gives |iota(delta)|^2 =
|iota(alpha)|^2 q_x^B. Repeat the construction on the real semisimple dual, whose
simple factors are duals with negated determinant weights in reverse order. This
gives the second certificate with weight -gamma_i, without using any Rankin bound.
All constructions are actual lisse Weil modules and determinant weights, so they
are global on the curve; the analytic affine restriction is not used here. -/
theorem native_exterior_certificates
    [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (hl : l ≠ D.p) (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hreal : NativeCondensedWeil.Real D l X₀ M iota)
    (Q : WeilModule D l X₀) (hQ : IsNonzeroSimpleSubquotient D l X₀ M Q) :
    ∃ w : ℝ, DeterminantWeight D l X₀ Q iota w ∧
      ExteriorBoundWitness D l X₀ Q iota w ∧
      ExteriorBoundWitness D l X₀
        (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) Q) iota (-w) :=
  by sorry

end WeilConjectures.NativeL2
