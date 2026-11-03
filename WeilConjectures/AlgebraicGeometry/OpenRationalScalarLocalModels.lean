/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.MapModScalarExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.CategoryTheory.SixFunctors.WeakSerreBoundedThick
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization

import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Rational scalar extension and finite constant local models

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

## Main statements

For each of the integral, subfield, and algebraic-closure maps, the `_homology` theorem
states an unconditional natural comparison; the companion theorem preserves bounded
constructibility, finite presentations, vanishing intervals, and every given local witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

set_option maxHeartbeats 2000000 in
-- The derived-module instances and canonical comparison traverse large monoidal structures.
private theorem scalar_extension_local_models
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ T))] :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ T)) ∧
      PreservesFiniteColimits (Mod.extendScalars (coefficientMap φ T)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
        constantModelBoundedConstructible Λ T K →
        constantModelBoundedConstructible Λ' T
          ((Mod.extendScalars (coefficientMap φ T)).leftDerivedFunctor.obj K)) ∧
      (∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        Λ,
        Mod.IsFinitelyPresented Λ P →
        Mod.IsFinitelyPresented Λ' ((Mod.extendScalars φ).obj P)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
        ∀ a b : ℤ,
          (∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) →
          ∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj
              ((Mod.extendScalars (coefficientMap φ T)).leftDerivedFunctor.obj K))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T),
        ∀ (Y : Scheme.{u}) (g : Y ⟶ T)
          (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (i : 𝒰.I₀),
          ∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
            Λ,
            Mod.IsFinitelyPresented Λ P →
            Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj
              ((CondensedRing.upperStar Λ g).obj M) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj
                P) →
            Mod.IsFinitelyPresented Λ' ((Mod.extendScalars φ).obj P) ∧
            Nonempty ((CondensedRing.upperStar Λ' (𝒰.f i)).obj
              ((CondensedRing.upperStar Λ' g).obj
                ((Mod.extendScalars (coefficientMap φ T)).obj M)) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod Λ').obj
                ((Mod.extendScalars φ).obj P))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T),
        IsConstantModelConstructible Λ T M →
        IsConstantModelConstructible Λ' T ((Mod.extendScalars (coefficientMap φ T)).obj M)) := by
  let G := (Mod.extendScalars (coefficientMap φ T))
  have hfp : ∀ P, Mod.IsFinitelyPresented _ P →
      Mod.IsFinitelyPresented _ ((Mod.extendScalars φ).obj P) := by
    intro P hP
    exact map_finitePresentation _ _ (Mod.extendScalars φ)
      (Mod.regularExtensionIso φ) P hP
  refine ⟨inferInstance, inferInstance, ?_, hfp, ?_, ?_, ?_⟩
  · intro K hK
    let e := G.leftDerivedFunctorIsoMapDerivedCategory
    let P : ObjectProperty _ :=
      IsConstantModelConstructible Λ' T
    have : P.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined
        Λ' T).1
    refine ⟨?_, fun q ↦ ?_⟩
    · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app K).symm
        (G.bounded_mapDerivedCategory_obj hK.1)
    · exact P.prop_of_iso
        ((G.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
          ((DerivedCategory.homologyFunctor _ q).mapIso (e.app K)).symm)
        (constant_model_scalar_extension φ T
          ((DerivedCategory.homologyFunctor _ q).obj K) (hK.2 q))
  · intro K a b h q hq
    let e := (Functor.isoWhiskerRight G.leftDerivedFunctorIsoMapDerivedCategory
      (DerivedCategory.homologyFunctor _ q) ≪≫
        (G.mapDerivedCategoryHomologyFunctorIso q).symm).app K
    exact (G.map_isZero (h q hq)).of_iso e
  · intro M Y g 𝒰 i P hP hmodel
    obtain ⟨eP⟩ := hmodel
    refine ⟨hfp P hP, ⟨?_⟩⟩
    exact (CondensedRing.upperStar _ (𝒰.f i)).mapIso
        (((CondensedRing.pullIso φ g).app M).symm) ≪≫
      ((CondensedRing.pullIso φ (𝒰.f i)).app
        ((CondensedRing.upperStar _ g).obj M)).symm ≪≫
      (Mod.extendScalars (coefficientMap φ (𝒰.X i))).mapIso eP ≪≫
      ((point_scalar_extension_iso φ (𝒰.X i)).app P).symm
  · intro M hM
    exact constant_model_scalar_extension φ T M hM

set_option maxHeartbeats 2000000 in
-- Isolate valuation-norm instances from the constant-model and derived-category proofs.
private theorem integral_extension_finite_limits
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact CondensedRing.integralScalarExtension_exact ℓ E.1 T

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Homology commutes naturally with the canonical integral scalar extension.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: coefficient flatness gives exactness. Identify the left derived functor with
its exact levelwise derived functor and compose with the natural homology comparison.
This comparison is natural on the entire unbounded derived category.
-/
theorem open_rational_scalar_local_models_integral_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) (q : ℤ) :
    Nonempty ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      T)).leftDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ (Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) T))) := by
  have : PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)) :=
    integral_extension_finite_limits ℓ E T
  let G := Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)
  exact ⟨Functor.isoWhiskerRight G.leftDerivedFunctorIsoMapDerivedCategory
    (DerivedCategory.homologyFunctor _ q) ≪≫ (G.mapDerivedCategoryHomologyFunctorIso q).symm⟩

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Canonical integral scalar extension retains the given local models.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: (1) use coefficient flatness for exactness and scalar extension for right
exactness; (2) the exact-derived homology comparison retains each vanishing interval;
(3) commute scalar extension with inverse image on the original stratum and cover;
(4) extend the specified scalar presentation matrix entry by entry; (5) ordinary
finite-presentation base change identifies its cokernel with the extension of the
same P; (6) assemble these witnesses on the unchanged strata, or every affine open.
-/
theorem open_rational_scalar_local_models_integral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)) ∧
      PreservesFiniteColimits (Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.padicIntegersRingObj.{u} ℓ E.1) T)),
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E.1) T K →
        constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E.1) T
          ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
            T)).leftDerivedFunctor.obj K)) ∧
      (∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.padicIntegersRingObj.{u} ℓ E.1),
        Mod.IsFinitelyPresented (Profinite.padicIntegersRingObj.{u} ℓ E.1) P →
        Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) ((Mod.extendScalars
          (padicIntegersRingObjToContinuousMapRingObj ℓ E)).obj P)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.padicIntegersRingObj.{u} ℓ E.1) T)),
        ∀ a b : ℤ,
          (∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) →
          ∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj
              ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
                T)).leftDerivedFunctor.obj K))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) T),
        ∀ (Y : Scheme.{u}) (g : Y ⟶ T)
          (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (i : 𝒰.I₀),
          ∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
            (Profinite.padicIntegersRingObj.{u} ℓ E.1),
            Mod.IsFinitelyPresented (Profinite.padicIntegersRingObj.{u} ℓ E.1) P →
            Nonempty ((CondensedRing.upperStar (Profinite.padicIntegersRingObj.{u} ℓ E.1) (𝒰.f
              i)).obj
              ((CondensedRing.upperStar (Profinite.padicIntegersRingObj.{u} ℓ E.1) g).obj M) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.padicIntegersRingObj.{u} ℓ E.1)).obj
                P) →
            Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) ((Mod.extendScalars
              (padicIntegersRingObjToContinuousMapRingObj ℓ E)).obj P) ∧
            Nonempty ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) (𝒰.f i)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) g).obj
                ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ
                E) T)).obj M)) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.continuousMapRingObj.{u} E.1)).obj
                ((Mod.extendScalars (padicIntegersRingObjToContinuousMapRingObj ℓ E)).obj P))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) T),
        IsConstantModelConstructible (Profinite.padicIntegersRingObj.{u} ℓ E.1) T M →
        IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E.1) T ((Mod.extendScalars
          (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)).obj M)) := by
  have : PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)) :=
    integral_extension_finite_limits ℓ E T
  have h := scalar_extension_local_models
    (Λ := Profinite.padicIntegersRingObj.{u} ℓ E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} E.1)
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) T
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Homology commutes naturally with the canonical subfield scalar extension.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: coefficient flatness gives exactness. Identify the left derived functor with
its exact levelwise derived functor and compose with the natural homology comparison.
This comparison is natural on the entire unbounded derived category.
-/
theorem open_rational_scalar_local_models_subfield_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : PadicAlgCl.FiniteIntermediateField ℓ) (hEF : E ≤ F)
    (T : Scheme.{u}) (q : ℤ) :
    Nonempty ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF)
      T)).leftDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjMap ℓ hEF) T))) := by
  let G := Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF) T)
  exact ⟨Functor.isoWhiskerRight G.leftDerivedFunctorIsoMapDerivedCategory
    (DerivedCategory.homologyFunctor _ q) ≪≫ (G.mapDerivedCategoryHomologyFunctorIso q).symm⟩

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Canonical subfield scalar extension retains the given local models.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: (1) use coefficient flatness for exactness and scalar extension for right
exactness; (2) the exact-derived homology comparison retains each vanishing interval;
(3) commute scalar extension with inverse image on the original stratum and cover;
(4) extend the specified scalar presentation matrix entry by entry; (5) ordinary
finite-presentation base change identifies its cokernel with the extension of the
same P; (6) assemble these witnesses on the unchanged strata, or every affine open.
-/
theorem open_rational_scalar_local_models_subfield
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : PadicAlgCl.FiniteIntermediateField ℓ) (hEF : E ≤ F)
    (T : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ
      hEF) T)) ∧
      PreservesFiniteColimits (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap
        ℓ hEF) T)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.continuousMapRingObj.{u} E.1) T)),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E.1) T K →
        constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} F.1) T
          ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF)
            T)).leftDerivedFunctor.obj K)) ∧
      (∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E.1),
        Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) P →
        Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} F.1) ((Mod.extendScalars
          (Profinite.padicSubfieldRingObjMap ℓ hEF)).obj P)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.continuousMapRingObj.{u} E.1) T)),
        ∀ a b : ℤ,
          (∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) →
          ∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj
              ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF)
                T)).leftDerivedFunctor.obj K))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj.{u} E.1) T),
        ∀ (Y : Scheme.{u}) (g : Y ⟶ T)
          (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (i : 𝒰.I₀),
          ∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
            (Profinite.continuousMapRingObj.{u} E.1),
            Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) P →
            Nonempty ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) (𝒰.f i)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) g).obj M) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.continuousMapRingObj.{u} E.1)).obj P)
                →
            Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} F.1) ((Mod.extendScalars
              (Profinite.padicSubfieldRingObjMap ℓ hEF)).obj P) ∧
            Nonempty ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} F.1) (𝒰.f i)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} F.1) g).obj
                ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF)
                T)).obj M)) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.continuousMapRingObj.{u} F.1)).obj
                ((Mod.extendScalars (Profinite.padicSubfieldRingObjMap ℓ hEF)).obj P))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj.{u} E.1) T),
        IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E.1) T M →
        IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} F.1) T ((Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF) T)).obj M)) := by
  have h := scalar_extension_local_models
    (Λ := Profinite.continuousMapRingObj.{u} E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} F.1)
    (Profinite.padicSubfieldRingObjMap ℓ hEF) T
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Homology commutes naturally with the canonical algebraic closure scalar extension.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: coefficient flatness gives exactness. Identify the left derived functor with
its exact levelwise derived functor and compose with the natural homology comparison.
This comparison is natural on the entire unbounded derived category.
-/
theorem open_rational_scalar_local_models_algebraic_closure_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) (q : ℤ) :
    Nonempty ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      T)).leftDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T))) := by
  let G := Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)
  exact ⟨Functor.isoWhiskerRight G.leftDerivedFunctorIsoMapDerivedCategory
    (DerivedCategory.homologyFunctor _ q) ≪≫ (G.mapDerivedCategoryHomologyFunctorIso q).symm⟩

set_option maxHeartbeats 400000 in
-- Elaborating the canonical coefficient and derived-module instances traverses large structures.
/-- Canonical algebraic closure scalar extension retains the given local models.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/
sk-prop-open-coefficients.proof.md,
rational paragraph (blueprint: lem-sfb-open-rational-scalar-local-models).

Proof: (1) use coefficient flatness for exactness and scalar extension for right
exactness; (2) the exact-derived homology comparison retains each vanishing interval;
(3) commute scalar extension with inverse image on the original stratum and cover;
(4) extend the specified scalar presentation matrix entry by entry; (5) ordinary
finite-presentation base change identifies its cokernel with the extension of the
same P; (6) assemble these witnesses on the unchanged strata, or every affine open.
-/
theorem open_rational_scalar_local_models_algebraic_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)) ∧
      PreservesFiniteColimits (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.continuousMapRingObj.{u} E.1) T)),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E.1) T K →
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) T
          ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
            T)).leftDerivedFunctor.obj K)) ∧
      (∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E.1),
        Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) P →
        Mod.IsFinitelyPresented (Profinite.padicAlgClRingObj.{u} ℓ) ((Mod.extendScalars
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj P)) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
            (Profinite.continuousMapRingObj.{u} E.1) T)),
        ∀ a b : ℤ,
          (∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) →
          ∀ q : ℤ, q < a ∨ b < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj
              ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
                T)).leftDerivedFunctor.obj K))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj.{u} E.1) T),
        ∀ (Y : Scheme.{u}) (g : Y ⟶ T)
          (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (i : 𝒰.I₀),
          ∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
            (Profinite.continuousMapRingObj.{u} E.1),
            Mod.IsFinitelyPresented (Profinite.continuousMapRingObj.{u} E.1) P →
            Nonempty ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) (𝒰.f i)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) g).obj M) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.continuousMapRingObj.{u} E.1)).obj P)
                →
            Mod.IsFinitelyPresented (Profinite.padicAlgClRingObj.{u} ℓ) ((Mod.extendScalars
              (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj P) ∧
            Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) (𝒰.f i)).obj
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) g).obj
                ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ
                E) T)).obj M)) ≅
              ((upperStarFromPoint (𝒰.X i)).mapMod (Profinite.padicAlgClRingObj.{u} ℓ)).obj
                ((Mod.extendScalars (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj P))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj.{u} E.1) T),
        IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E.1) T M →
        IsConstantModelConstructible (Profinite.padicAlgClRingObj.{u} ℓ) T ((Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).obj M)) := by
  have h := scalar_extension_local_models
    (Λ := Profinite.continuousMapRingObj.{u} E.1)
    (Λ' := Profinite.padicAlgClRingObj.{u} ℓ)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2

end AlgebraicGeometry.ProEtale
