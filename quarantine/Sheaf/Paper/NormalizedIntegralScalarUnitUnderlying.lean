/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData

/-! # Integral normalization of a restricted scalar unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Multiplication normalization gives the specified integral scalar-unit arrow.
Source: exceptional coefficient construction, integral identity clause; Stacks Project,
Tags 03DA, 06YY and 07A6
(blueprint: lem-sf-normalized-integral-scalar-unit-underlying).

Proof: use hS to identify the underlying scalar objects. The two ordinary derived
extension presentations select the same normalized universal tensor witness.
On a flat-term K-flat representative, the scalar adjunction unit sends x to 1 tensor x;
identity restriction has identity section functions. Tensor multiplication sends
s tensor x to s*x and is inverse to this unit. The adjunction Hom bijection therefore
identifies the transported PurCompactSupport.tensorIdentity with the ordinary
K-flat multiplication unitor. The equality h supplies the identity-map transport;
its particular proof is irrelevant. Naturality and localization of good complexes
extend this calculation to every derived object. The hypothesis hχ identifies
S.realization.inv with the ordinary-to-completed comparison. Invert the isomorphisms
using the object equality from hS, and substitute into e.normalized. The resulting
arrow is chi.inv followed by the ordinary multiplication unitor, namely the
completed unit. The identity clause of CompletedLineTensor.canonical_restriction
identifies this arrow with the underlying sfIntegralScalarUnit component on the
unchanged intrinsic integral representative. These arguments include zero objects
and require no geometric characteristic assumption on T. -/
theorem normalized_integral_scalar_unit_underlying
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral E)
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)) T)
    (hS : S.functor ⋙ RingStage.inclusion.{u, v} l Ω T (.integral E) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T)
    (hχ : ∀ K : C.{u, v} l Ω T (.integral E),
      HEq (S.realization.inv.app K)
        ((completedScalarComparison l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T).app K.obj))
    (h : ∀ W : Scheme.{max u v},
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)).map W = 𝟙 _)
    (e : ScalarIdentity.{u, v} l Ω h T S)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((e.iso.hom.app K).hom)
      (((sfIntegralScalarUnit l E.carrier T 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K)).hom) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
