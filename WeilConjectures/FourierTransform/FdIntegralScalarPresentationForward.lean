/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractAssembly
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

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

section Atoms

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
  (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    FdOrdinaryScalarTransport l Ω T h)

/-- On every integral object the comparison is the inverse derived ordinary square followed
by the normalized ordinary-to-completed comparison. -/
private theorem lift_formula
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b)
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((b h).hom.app K).hom ≫ (eqToIso (stage L).integral_identity).hom.app ((U l Ω T h).obj K) =
      (pbcAmbientScalarExtension l Ω T h).map ((eqToIso (stage E).integral_identity).hom.app K) ≫
        (FdIntegralScalarForward.eD l Ω T h (ordinary h)).inv.app K.obj ≫
        (integralDetailedTransport T l _).map
          ((sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T).hom.app K) := by
  sorry

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- The completed associator through the ordinary-to-completed comparisons. -/
private theorem integralAssoc_hom {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((integralAssoc l Ω T h k).hom.app K).hom =
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω k) T).inv.app
          ((U l Ω T h).obj K) ≫
        (integralOrdinaryDerivedScalar l _ _ (pbcFiniteFieldInclusion l Ω k) T).map
          ((sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T).inv.app K) ≫
        (FdIntegralScalarForward.ODcomp l Ω T h k).hom.app K.obj ≫
        (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T).hom.app
          K := by
  sorry

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- The completed unit through the ordinary-to-completed comparison. -/
private theorem integralUnit_hom (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((integralUnit l Ω T E).hom.app K).hom =
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T).inv.app
          K ≫
        (eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω E) ι T) (FdIntegralScalarForward.inclusion_id l Ω E)) ≪≫
          integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app K.obj := by
  sorry

/-- The normalized derived ordinary square is compatible with the units. -/
private theorem eD_unit (E : Padic.FiniteCoefficientFields l Ω)
    (o : FdOrdinaryScalarTransport l Ω T (le_refl E))
    (Y : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) T)) :
    (FdIntegralScalarForward.eD l Ω T (le_refl E) o).inv.app Y ≫
        (integralDetailedTransport T l _).map
          ((eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l
            (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E) ι T)
            (FdIntegralScalarForward.inclusion_id l Ω E)) ≪≫
            integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app Y) =
      (pbcAmbientScalarUnit l Ω T E).hom.app ((integralDetailedTransport T l _).obj Y) := by
  sorry

end Atoms

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
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
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
        ((I l Ω T stage E).obj K)) := by
  refine ⟨fun {E L M} h k K ↦ ?_, fun E K ↦ ?_⟩
  · exact FdIntegralScalarForward.assoc_assembly
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T)
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T)
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω M) T)
      _ _ _ (I l Ω T stage E) (I l Ω T stage L) (I l Ω T stage M)
      (integralDetailedTransport T l _) (integralDetailedTransport T l _)
      (integralDetailedTransport T l _)
      (eqToIso (stage E).integral_identity) (eqToIso (stage L).integral_identity)
      (eqToIso (stage M).integral_identity)
      _ _ _ _ _ _ (pbcAmbientScalarExtension l Ω T h) (pbcAmbientScalarExtension l Ω T k)
      (pbcAmbientScalarExtension l Ω T (h.trans k)) _ _ _
      (b h) (b k) (b (h.trans k)) (integralAssoc l Ω T h k)
      (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k)
      (pbcAmbientScalarAssociator l Ω T h k)
      (pbcIntegralScalarAssociator_hom l Ω T dT.out iT.out h k)
      _ _ _ (FdIntegralScalarForward.ODcomp l Ω T h k)
      (FdIntegralScalarForward.eD l Ω T h (ordinary h))
      (FdIntegralScalarForward.eD l Ω T k (ordinary k))
      (FdIntegralScalarForward.eD l Ω T (h.trans k) (ordinary (h.trans k)))
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T)
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω k) T)
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T)
      (lift_formula l Ω T stage ordinary b hlift h) (lift_formula l Ω T stage ordinary b hlift k)
      (lift_formula l Ω T stage ordinary b hlift (h.trans k))
      (integralAssoc_hom l Ω T h k)
      (FdIntegralScalarForward.eD_cocycle l Ω T h k (ordinary h) (ordinary k)
        (ordinary (h.trans k))) K
  · exact FdIntegralScalarForward.unit_assembly
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T) _ (I l Ω T stage E)
      (integralDetailedTransport T l _) (eqToIso (stage E).integral_identity)
      _ _ (pbcAmbientScalarExtension l Ω T (le_refl E)) _ (b (le_refl E))
      (integralUnit l Ω T E) (pbcIntegralScalarUnit l Ω T dT.out iT.out E)
      (pbcAmbientScalarUnit l Ω T E) (pbcIntegralScalarUnit_hom l Ω T dT.out iT.out E) _
      (fun Y ↦
      (eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω E) ι T) (FdIntegralScalarForward.inclusion_id l Ω E)) ≪≫
        integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app Y)
      (FdIntegralScalarForward.eD l Ω T (le_refl E) (ordinary (le_refl E)))
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T)
      (lift_formula l Ω T stage ordinary b hlift (le_refl E)) (integralUnit_hom l Ω T E)
      (eD_unit l Ω T E (ordinary (le_refl E))) K

end WeilConjectures
