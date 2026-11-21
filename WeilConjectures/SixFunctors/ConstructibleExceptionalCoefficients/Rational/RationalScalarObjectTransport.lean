/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData

/-! # Object transport for rational scalar identity -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Rational scalar extension maps the localization of an integral object to the
localization of the corresponding integral scalar functor object. -/
theorem rational_scalar_object_transport
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (S : C.{u, v} l Ω T (.integral E) ⥤ C.{u, v} l Ω T (.integral E))
    (hS : S ⋙ RingStage.inclusion.{u, v} l Ω T (.integral E) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T)
    (K : C.{u, v} l Ω T (.integral E)) :
    (rationalScalar.{u, v} l Ω E E (AlgHom.id (Padic l) E.carrier) T).obj
        ((rationalization.{u, v} l Ω E T).obj K) =
      (rationalization.{u, v} l Ω E T).obj (S.obj K) := by
  refine (sfRationalScalarExtension_obj l E.carrier T 0
    (Fact.out : l.Prime).ne_zero E.carrier (AlgHom.id (Padic l) E.carrier) _).trans ?_
  apply congrArg (sfRationalConstructibleLocalization l E.carrier T).obj
  apply ObjectProperty.FullSubcategory.ext
  exact (Functor.congr_obj hS K).symm

end WeilConjectures.ConstructibleExceptionalCoefficients
