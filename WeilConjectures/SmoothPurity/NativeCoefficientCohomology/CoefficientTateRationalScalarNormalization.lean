/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTatePowerScalar
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateCompletedBasis
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateOrdinaryScalarSquare
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateScalarDescent
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateZeroNormalization

/-! # Rational descent of a normalized root frame

This comparison retains the finite root frames and their proved scalar formula.
It concerns the unshifted line at one finite coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.NativeCoefficientCohomology

/-- The canonical invertibility witness on the geometric fibre.
Source: finite-field coefficient convention
(blueprint: lem-sf-coefficient-tate-rational-scalar-normalization). -/
local instance coefficientRationalTateResidueUnits (P : PurityFiniteSetting.{u})
    (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    ∀ x : (P.field.geometricFiber X₀).left,
      Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x

set_option maxHeartbeats 1500000 in
-- The normalized comparisons unfold several completed and derived coefficient functors.
/-- The normalized completed root basis descends to the rational coefficient line.

Source: the construction of E(m) in the coefficient-twist conventions,
the current blueprint's `def-weil-frobenius-coefficient-twists.md`;
Weil I (2.2), geometric Frobenius on roots of unity.
(blueprint: lem-sf-coefficient-tate-rational-scalar-normalization)

Proof: at modulus l^n use the frame map sending the constant residue a to z_n^a.
Its value formula and z_(n+1)^l=z_n identify the transition squares on constant
sections, hence on their sheafifications. The resulting isomorphism of root
systems induces an isomorphism of their limits. On the scalar limit it is linear:
project the scalar identity to each finite residue module and use joint
injectivity of the limit projections. Thus the completed root module is the
rank-one regular completed integer module with its specified frame, rather than
an unspecified locally free module. Extend this map along the completed scalar
map to the coefficient integers. The normalized integral extension comparison
identifies this scalar extension with purTwistIntegralModule. Its formula on
pure tensors identifies the chosen basis with the published integral generator.

Tensor these maps in the prescribed order. Use regular-module multiplication
for the degree-zero and successor identifications. Every finite coordinate of a
source or target basis root is the constant residue one. The given frame power
law therefore shows that q^d times the published positive-line map on each pure
generator equals the transported coefficient-unit map. The sheaf scalar-extension
and tensor universal properties make these generators detect maps locally.
Consequently this is an equality of module-sheaf maps, not just of global
sections. Apply the degree-zero single-complex functor. The completed-to-ordinary
derived comparison and its inverse-image naturality identify this map with the
actual integral root-line Frobenius comparison. For the regular coefficient the
strict Roos unit normalization identifies the same comparison with the published
constant Weil structure. Pass to the constructible full subcategory and apply
the additive rationalization functor, which preserves the displayed q^d scalar
equality. The two derived comparison squares give the stated rational square.
The degree-zero tensor is the regular unit with scalar one. For an empty scheme
all section maps and the resulting derived equalities have the same formulas. -/
theorem coefficient_tate_rational_scalar_normalization
    (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : CoefficientTateRootFrames (P.field.geometricFiber X₀).left P.coefficients.l
      (Nat.card P.field.k₀) (P.field.geometricFrobenius X₀).hom)
    (hpower : CoefficientTateFramePowerScalarLaw P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar))
      (P.field.geometricFrobenius X₀).hom (Nat.card P.field.k₀) A)
    (d : ℕ) :
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u}
      P.coefficients.l P.coefficients.Qbar
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
    let K := FrobeniusCoefficientTwists.rationalWeilLine P.field P.coefficients.l
      P.coefficients.different X₀ E (d : ℤ)
    let U := constantWeilRationalComplex P.coefficients.l E P.field
      P.coefficients.different X₀
    ∃ b : K.carrier ≅ U.carrier,
      (Nat.card P.field.k₀ ^ d) • (K.str.hom ≫ b.hom) =
        (sfWeilFrobeniusPullback P.field P.coefficients.l
          P.coefficients.different X₀ E).map b.hom ≫ U.str.hom := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u}
    P.coefficients.l P.coefficients.Qbar
    (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
  let S := (P.field.geometricFiber X₀).left
  let g := (P.field.geometricFrobenius X₀).hom
  let q := Nat.card P.field.k₀
  obtain ⟨z, hz, b, hb⟩ := coefficient_tate_completed_basis P.coefficients.l E S q g A d
  have hs := coefficient_tate_ordinary_scalar_square P.coefficients.l E S g q A
    hpower d z hz b hb
  obtain ⟨c, hc⟩ := coefficient_tate_scalar_descent P.coefficients.l E S g q d b hs
  refine ⟨c, ?_⟩
  have hzero := coefficient_tate_zero_normalization P.coefficients.l E g
  have htheta :
      (FrobeniusCoefficientTwists.rationalDerivedLineMap P.coefficients.l E g 0).hom =
        (constantWeilRationalTheta P.coefficients.l E P.field
          P.coefficients.different X₀).hom := by
    dsimp only [FrobeniusCoefficientTwists.rationalDerivedLineMap,
      constantWeilRationalTheta, constantWeilConstructibleIntegralTheta,
      Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    congr 1
    congr 1
    apply ObjectProperty.hom_ext
    exact hzero
  change q ^ d • ((FrobeniusCoefficientTwists.rationalDerivedLineMap
      P.coefficients.l E g (d : ℤ)).hom ≫ c.hom) =
    (rationalDerivedPullback P.coefficients.l E g).map c.hom ≫
      (constantWeilRationalTheta P.coefficients.l E P.field
        P.coefficients.different X₀).hom
  rw [← htheta]
  exact hc

end WeilConjectures.NativeCoefficientCohomology
