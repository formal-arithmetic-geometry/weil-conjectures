/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.CompletedCoefficientPresentationTransport
import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Generator-normalized scalar transport through the coefficient presentation

Source: Bhatt--Scholze 3.4.12, 3.5.1 and 6.8.2; trace-definition coefficient comparison
(blueprint: lem-fd-coefficient-scalar-lift-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The ordinary coefficient-presentation comparison, composed with the actual
quotient-map completion, gives the required integral scalar lift.
Source: trace-definition coefficient-category sentence, normalized integral
completion comparison proof steps 2 and 3; Bhatt--Scholze 3.4.12, 3.5.1 and 6.8.2
(blueprint: lem-fd-coefficient-scalar-lift-normalization).

Proof: the completed coefficient isomorphisms commute with every finite projection.
Their scalar square therefore commutes. The balanced tensor comparison transports
each tensor generator by precisely these coefficient isomorphisms; its inverse
uses their inverses, and both composites are identities on generators, hence on
the sheafified tensor product. This constructs o. Derive this isomorphism using
the canonical counits, as in purScalarModel_existsUnique. Restrict its inverse
to the integral constructible source, and compose with coefficient transport of
the actual completedScalarComparison. This is invertible because the source is
derived complete and strict scalar extension preserves constructibility. On a
flat-term K-flat representative substitute the counit normalization of the
ordinary transport and the localization equation of completedScalarComparison.
Naturality moves coefficient transport factors across these maps. Cancellation
of the two inverse ordinary tensor comparisons leaves exactly o.completion.
Its quotient coordinates are the actual projections and its shifted-product
coordinate is zero; uniqueness of descent makes the equation independent of the
representative. -/
theorem fdCoefficientScalarLift_normalization
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∀ {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B),
      ∃ (o : FdOrdinaryScalarTransport l Ω T h)
        (a : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω A) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        sfConstructibleIntegralScalarExtension D.p l hl (pbcFiniteField.{u} l Ω A)
          (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω B) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)),
      ∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω A) T).FullSubcategory)
        (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T
          (DerivedCategory.Q.obj P.obj)),
      HEq (a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω B) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω A) T).hom.app P.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω A) T).mapHomologicalComplex
            (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (o.completion l Ω P.obj)) := by sorry

end WeilConjectures
