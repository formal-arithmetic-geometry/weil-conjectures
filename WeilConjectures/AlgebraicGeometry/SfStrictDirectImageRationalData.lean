/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageScalarCoherence
public import WeilConjectures.AlgebraicGeometry.PbcRationalTransport

/-! # Explicit tensor-Hom rationalization of the integral direct image

Source: strict direct-image scalar comparison, Step 8.
(blueprint: def-sf-strict-direct-image-rational-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage transition associator unitor)

/-- Extend the actual integral image on Hom modules by the localized coefficient ring.
This is a construction, independent of the unproved coherence descent.
Source: scalar-comparison proof, Step 8; raw scalar localization.
(blueprint: def-sf-strict-direct-image-rational-data) -/
def rationalImage {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) (E : Index l Ω) : Stage l Ω Z E ⥤ Stage l Ω X E :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E)) (D.integral E).image

/-- The actual tensor-Hom direct image preserves addition.
Source: scalar-comparison proof, Step 8.
(blueprint: def-sf-strict-direct-image-rational-data) -/
instance rationalImageAdditive {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) (E : Index l Ω) : (rationalImage l Ω f D E).Additive :=
  ScalarLocalization.transportAdditive _ _ _

end WeilConjectures.SfStrictDirectImageScalar
