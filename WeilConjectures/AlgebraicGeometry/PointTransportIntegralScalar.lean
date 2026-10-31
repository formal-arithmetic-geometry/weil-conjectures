/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantGeometricStalkData

/-! # Scalar extension of iterated point transport

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
step 8 (blueprint: lem-zl-point-transport-integral-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstantGeometricStalkUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Iterated point transport commutes with integral-to-field scalar extension.
Source: reviewed expansion step 8 (blueprint: lem-zl-point-transport-integral-scalar).

Proof: for one transport, substitute its definition as integral transport tensored
with E, conjugated by pointRationalFibreObjIso and the size-descent comparison.
Naturality of the size-descent counit cancels these boundary isomorphisms and leaves
the displayed square with localPullbackObjectIso. Induct on the positive-power
index. In the successor step use the one-step square, then the induction square
at the pulled-back integral object. Expand localPullbackComposition, which is the
localized integral compositor with the same object comparisons. Its inverse
cancels the intermediate object comparisons. Functoriality of scalar extension
and naturality of the size-descent counit give the next square. Finally specialize
to the integral stalk of the constant object and its prescribed object comparison.
No returning point, Weil map, or local endomorphism identity is used. -/
theorem pointTransport_integral_scalar
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ) :
    (pointFibreModuleLift E).mapDerivedCategory.map
        (localPointTransportIterate l E D hl
          (localDerivedStalk l E D hl Y₀
            (constantWeilRationalComplex l E D hl Y₀) x) r).hom ≫
      (rationalTransportComparison l E D hl Y₀ x r).hom =
    (rationalFibreComparison l E D hl Y₀ x).hom ≫
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map
          (integralTransportIterate l E D hl (integralStalk l E D hl Y₀ x) r) := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
