/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty

/-! # Forward coherence of the integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

/-- Forward scalar associativity and the multiplication/completeness unit for
an integral comparison characterized by its good-representative completion lift.
Source: trace-definition coefficient comparison, integral steps 4--6
(blueprint: lem-fd-integral-scalar-presentation-forward).

Proof: Choose the normalized ScalarCompletionAssociatorData. On a good K-flat
representative the lift equation identifies b with the actual chi map after
ordinary coefficient-presentation transport: cancel the scalar-representative
comparison and the coefficient-transport factor in that equation. The generator
normalization of ordinary identifies its derived transport with
fdIntegralOrdinaryPresentation. Naturality along resolving isomorphisms extends
this identification to every integral object. Apply the forward equation of
fdIntegralInverseScalarCocycle to these same chi maps. Naturality of chi for the
second extension at the first chi map replaces chi at the ordinary extension
followed by completed extension of chi with ordinary extension of chi followed
by chi at the completed extension. Under coefficient transport,
fdIntegralOrdinaryBalancing identifies ordinary balancing with pbcAmbientScalarComp.
The specified framework associator is normalized by the same completion maps,
as recorded by integralPullbackComparisonRealization. Insert the stage
integral_identity casts; direct versus composite field embeddings are identified
by coefficientInclusion_laws. Map the requested equation through the faithful
PBC integral inclusion. These identifications turn it into that forward equation,
so faithfulness proves it. For an equal-field inclusion use
fdIntegralInverseScalarUnits: chi is ordinary multiplication followed by inverse
completeness. Ordinary generator transport preserves multiplication. Cancel the
completion unit to obtain b followed by I of integralUnit equal to
pbcIntegralScalarUnit. This argument includes zero objects and repeated fields;
no strict-inclusion assumption is used.
-/
theorem fdIntegralScalarPresentationForward
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b) :
    (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (C l Ω T k).map ((b h).hom.app K) ≫
        (b k).hom.app ((U l Ω T h).obj K) ≫
        (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) =
      (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) ≫ (b (h.trans k)).hom.app K) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).hom.app K ≫
        (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K) =
      (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app
        ((I l Ω T stage E).obj K)) := by sorry

end WeilConjectures
