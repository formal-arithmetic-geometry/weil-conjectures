/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkData

/-! # Scalar extension of return and Weil factors

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
step 8 (blueprint: lem-zl-return-weil-integral-scalar).
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

/-- The return and iterated Weil factors commute with integral scalar extension.
Source: reviewed expansion step 8 (blueprint: lem-zl-return-weil-integral-scalar).

Proof: the rational constant Weil map is the image of the integral Weil map under
the constructible localization, with its prescribed pullback object comparison.
Induct on the positive-power index to identify the iterated Weil maps: substitute
the localized integral formula for localPullbackComposition and use functoriality.
For the return comparison substitute the same formula on each side of the return
equality. Equality elimination handles its central eqToIso without any assumption
that the geometric point itself is fixed. Apply the point fibre functor. Its
localization comparison is natural on localized integral morphisms, by the pure
tensor formula for pointRationalFibre. Apply the size lift and the naturality of
its counit to obtain the displayed comparison in the ambient derived category.
The remaining two boundary comparisons are exactly rationalTransportComparison
and rationalFibreComparison. This argument does not use point transport. -/
theorem returnWeil_integral_scalar
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :
    (pointFibreModuleLift E).mapDerivedCategory.map
        (((pointRationalFibre D l hl E).map
          ((localReturnComparison l E D hl Y₀
            (constantWeilRationalComplex l E D hl Y₀) x r h).hom ≫
            (@rationalDerivedPullback l _ E _ _ _ _ _ x
              (frobeniusPointPrimeInvertible D l hl)
              (sfWeilPrimeInvertible D l hl Y₀)).map
                (localWeilIterate l E D hl Y₀
                  (constantWeilRationalComplex l E D hl Y₀) r).hom)).hom) ≫
      (rationalFibreComparison l E D hl Y₀ x).hom =
    (rationalTransportComparison l E D hl Y₀ x r).hom ≫
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map
          (integralReturnWeil l E D hl Y₀ x r h) := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
