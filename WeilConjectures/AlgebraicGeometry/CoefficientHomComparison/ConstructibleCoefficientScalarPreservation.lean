/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.CoefficientHomCoefficientIso
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.IntegralCoefficientHomReductions
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Constructibility under the four specified coefficient extensions -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- All specified coefficient extensions preserve bounded finite constant models.
Source: Bhatt--Scholze 6.8.13--15 and Hemo--Richarz--Scholbach Theorem 7.7;
Steps 3 and 5 of lem-per-constructible-coefficient-hom-comparison.
Proof: the integral criterion and finite-level propagation give preservation by each
positive finite quotient. For inversion first transport to the embedded integral ring
using integralIso. The existing integral-to-field scalar functor preserves ordinary
bounded constructibility, and the adic predicate comparison identifies both predicates.
The scalar tower identifies this composite with integralToField. Finite field extension
and extension to the algebraic closure preserve ordinary bounded constructibility by
the corresponding scalar-extension theorems; apply the same predicate comparisons.
All transports are isomorphisms in the ordinary ambient derived categories.
(blueprint: lem-per-constructible-coefficient-scalar-preservation). -/
theorem constructible_coefficient_scalar_preservation
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
      (K : D X (integral.{u} ℓ E)), bc X (integral ℓ E) K →
        bc X (finite ℓ E n) ((scalar X (reductionMap ℓ E n)).obj K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : D X (integral.{u} ℓ E)), bc X (integral ℓ E) K →
        bc X (Profinite.continuousMapRingObj E.val)
          ((scalar X (integralToField ℓ E)).obj K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : D X (Profinite.continuousMapRingObj.{u} E.val)),
      bc X (Profinite.continuousMapRingObj E.val) K →
        bc X (Profinite.continuousMapRingObj F.val)
          ((scalar X (Profinite.padicSubfieldRingObjMap ℓ h)).obj K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : D X (Profinite.continuousMapRingObj.{u} E.val)),
      bc X (Profinite.continuousMapRingObj E.val) K →
        bc X (Profinite.padicAlgClRingObj ℓ)
          ((scalar X (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj K)) := by
  have hfield (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.val) X) =
        bc X (Profinite.continuousMapRingObj E.val) :=
    (adicConstructibilityPredicateComparison ℓ X _ (.continuous E.val)).2
  have hintegral (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) =
        bc X (Profinite.padicIntegersRingObj ℓ E.val) :=
    (adicConstructibilityPredicateComparison ℓ X _ (.integral E.val)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E n K hK
    exact ((integral_coefficient_hom_reductions X ℓ E K hK).2 n).1
  · intro E K hK
    let M := (scalar X (integralIso ℓ E).inv).obj K
    let : IsMonHom (integralIso ℓ E).symm.hom := by
      change IsMonHom (integralIso ℓ E).inv
      infer_instance
    have hM := coefficient_iso_preserves_bc X (integralIso ℓ E).symm K hK
    have hM' : boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) M := by
      rwa [hintegral]
    have ht := boundedConstructible_derivedExtendScalars_obj X ℓ E ⟨M, hM'⟩
    rw [hfield] at ht
    have : (constantModelBoundedConstructible
        (Profinite.continuousMapRingObj E.val) X).IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined _ X).2.1
    exact (constantModelBoundedConstructible _ X).prop_of_iso
      ((scalarTower X (integralIso ℓ E).inv
        (padicIntegersRingObjToContinuousMapRingObj ℓ E)).app K).symm ht
  · intro E F h K hK
    rw [← hfield] at hK ⊢
    exact boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h ⟨K, hK⟩
  · intro E K hK
    rw [← hfield] at hK
    change constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X _
    rw [← (adicConstructibilityPredicateComparison ℓ X _ .algebraicClosure).2]
    exact boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E ⟨K, hK⟩

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
