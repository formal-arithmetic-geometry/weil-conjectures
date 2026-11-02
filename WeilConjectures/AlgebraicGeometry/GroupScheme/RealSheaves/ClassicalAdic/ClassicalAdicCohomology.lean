/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.ConstructibleCoefficientHomComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.CategoryTheory.Skeletal
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
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
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
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
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison

/-! # Classical adic cohomology of a constructible Weil complex

Source: latest blueprint, part-weights-riemann-hypothesis/sec-rank-one-curves/
sec-the-jacobian-and-frobenius-invariants/sk-prop-wrp-h1-no-fixed/d-real-cohom.md,
Comparison with the classical description (blueprint: prop-wf-classical-adic-cohomology).

The helpers expose existing coefficient transports and bundle the displayed comparisons.
All finite levels are positive: the sequence index n denotes the quotient by pi^(n+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace RealSheaves

/-- The existing finite-field datum underlying the chapter setup.
Source: d-real-setup and the comparison paragraph
(blueprint: prop-wf-classical-adic-cohomology). -/
def Setup.adicFieldDatum (D : Setup.{u, v}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := D.p
  a := D.a
  q := D.q
  prime := D.p_prime
  exponent_pos := D.a_pos
  cardinality_eq := rfl
  k₀ := D.k₀
  card_base := Nat.card_eq_fintype_card.trans D.card_eq
  k := D.k

/-- Geometric Frobenius g_C = id × Spec(φ_q⁻¹) on the chapter's chosen fibre product:
exactly the recorded `FiniteFieldDatum.geometricFrobenius` of def-weil-frobenius-detailed,
which def-weil-weil-sheaf-complex uses for Weil structures; no second definition.
Source: d-real-setup, geometric Frobenius convention; def-weil-frobenius-detailed
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev Setup.adicFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) : Aut (D.geometricCurve C₀) :=
  @WeilConjectures.FiniteFieldDatum.geometricFrobenius D.adicFieldDatum
    (Over.mk (C₀ ↘ Spec (.of D.k₀))) hC.2.2.2.1 hC.2.2.2.2.1

namespace ClassicalAdic

/-- The canonical spectral integral-to-field map is the existing coefficient comparison.
Source: comparison paragraph (blueprint: prop-wf-classical-adic-cohomology). -/
abbrev integralToField := AlgebraicGeometry.ProEtale.CoefficientHomComparison.integralToField

/-- Derived coefficient change on the actual pulled-back coefficient sheaves.
Source: comparison paragraph, scalar extension
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev extend {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor

/-- Derived scalar extension on coefficient complexes, using the induced global ring map.
Source: comparison paragraph, the coefficient-valued displayed formulas
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev extendSections {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] :=
  letI := ModuleCat.extendScalars_preservesKFlatQuasiIso (CategoryTheory.MonObj.Γ.map φ)
  (ModuleCat.extendScalars (CategoryTheory.MonObj.Γ.map φ)).leftDerivedFunctor

/-- The two coefficient-complex scalar comparisons, for one specified coefficient change.
Source: comparison paragraph, the rational and finite formulas and their compact analogues
(blueprint: prop-wf-classical-adic-cohomology). -/
def ScalarComparisons {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) : Prop :=
  Nonempty ((extendSections φ).obj
      ((CondensedRing.condensedRingOrdinaryCoefficientComplex Λ a).obj K) ≅
    (CondensedRing.condensedRingOrdinaryCoefficientComplex Λ' a).obj L) ∧
  Nonempty ((extendSections φ).obj
      ((CondensedRing.condensedRingCompactCoefficientComplex Λ c).obj K) ≅
    (CondensedRing.condensedRingCompactCoefficientComplex Λ' c).obj L)

/-- The finite-level comparison retains the quotient-ring action in every calculation.
The normalized encoding is the existing section-action equivalence; quantification over
its witnesses avoids choosing an arbitrary presentation. Both compact calculations use
exactly the supplied compactification.
Source: comparison paragraph, finite torsion levels
(blueprint: prop-wf-classical-adic-cohomology). -/
def EtaleComparisons (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) : Prop :=
  ∀ (eX : FiniteDiscreteOrdinary.Encoding A X)
    (eY : FiniteDiscreteOrdinary.Encoding A Y),
    let M := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let L := eX.fixedDerived.functor.obj K
    IsIso ((derivedComparisonAdjunction M X).counit.app L) ∧
    Nonempty ((comparisonUpperStar M Y).mapDerivedCategory.obj
      ((Etale.lowerStar M a).rightDerivedFunctor.obj
        ((comparisonLowerStar M X).rightDerivedFunctor.obj L)) ≅
      eY.fixedDerived.functor.obj
        (((CondensedRing.lowerStar
          (FiniteDiscreteOrdinary.coefficient A) a).rightDerivedFunctor).obj K)) ∧
    Nonempty ((comparisonUpperStar M Y).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekOfCompactification M c).obj
        ((comparisonLowerStar M X).rightDerivedFunctor.obj L)) ≅
      eY.fixedDerived.functor.obj
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (FiniteDiscreteOrdinary.coefficient A) c).obj K))

/-- Reconstruction with the canonical derived quotient projections, not an unspecified cone.
Source: comparison paragraph, RΓ commuting with derived limits and the compact analogue
(blueprint: prop-wf-classical-adic-cohomology). -/
def TowerReconstruction (D : Setup.{u, v})
    (E : PadicAlgCl.FiniteIntermediateField D.l) (X : Scheme.{u})
    (F : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (CategoryTheory.MonObj.Γ (DerivedNakayama.integerRing D.l (ULift.{u} E.val)))))
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X)) : Prop :=
  ∃ δ : (∏ᶜ fun n ↦ F.obj
      (AdicCompletion.integralLevel D.l (ULift.{u} E.val) X K n)) ⟶ (F.obj K)⟦(1 : ℤ)⟧,
    IsDerivedLimitTriangle
      (K := fun n ↦ F.obj (AdicCompletion.integralLevel D.l (ULift.{u} E.val) X K n))
      (fun n ↦ F.map (AdicCompletion.integralStep D.l (ULift.{u} E.val) X K n))
      (F.obj K)
      (Pi.lift (fun n ↦ F.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient D.l (ULift.{u} E.val) X n)).unit.app K))) δ

end ClassicalAdic

/-- Classical adic reconstruction for ordinary and compact cohomology of a Weil complex.

Source: latest blueprint, part-weights-riemann-hypothesis/sec-rank-one-curves/
sec-the-jacobian-and-frobenius-invariants/sk-prop-wrp-h1-no-fixed/d-real-cohom.md,
Comparison with the classical description
(blueprint: prop-wf-classical-adic-cohomology).

Proof: (1) Forget the Weil structure. The finite-extension two-colimit gives E and K_E;
the integral-model generators and rationalization comparison give an integral K_0.
(2) The integral criterion gives completeness and finite Tor amplitude. Apply scalar-six
to O_E -> E -> Qbar and to the positive uniformizer quotients. Exact terminal sections
over the algebraically closed point, and ringed evaluation on flat/Koszul models, give
the coefficient-complex comparisons, compatibly with the quotient maps.
(3) Completeness identifies K_0 with its derived reduction tower. Global derived Hom
from the regular unit preserves derived limits, yielding ordinary reconstruction.
(4) For compact support, constructibility stability makes Ra_! K_0 complete on the point.
Apply the same limit argument there and identify its reductions by scalar-six; this
does not assert that Ra_! preserves arbitrary inverse limits.
(5) Finite admissible comparison identifies each positive level and both operations
with the etale calculations using the same compactification.
(6) Substitute the limit descriptions in the rational scalar comparisons and take H^i.
This is the classical adic construction in every degree, without interchanging H^i
and an underived inverse limit. Qbar is represented by the existing PadicAlgCl model;
the chapter's chosen algebraic closure is identified with it over Q_l.
-/
theorem classicalAdicCohomology (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (c : Compactification
      (pullback.snd (C₀ ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    (K : WeilConjectures.condensedWeilComplex (Profinite.padicAlgClRingObj D.l)
      (D.adicFrobenius C₀ hC).hom) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField D.l)
      (K_E : BoundedConstructible (condensedRingObj
        (Profinite.continuousMapRingObj E.val) (D.geometricCurve C₀)))
      (K₀ : BoundedConstructible (AdicCompletion.ring D.l (ULift.{u} E.val)
        (D.geometricCurve C₀))),
      Nonempty ((ClassicalAdic.extend (Profinite.padicSubfieldRingObjToPadicAlgCl D.l E)
          (D.geometricCurve C₀)).obj K_E.obj ≅
        ((WeilConjectures.condensedWeilForget (Profinite.padicAlgClRingObj D.l)
          (D.adicFrobenius C₀ hC).hom).obj K).obj) ∧
      Nonempty ((ClassicalAdic.extend
          (AlgebraicGeometry.ProEtale.CoefficientHomComparison.integralToField D.l E)
          (D.geometricCurve C₀)).obj K₀.obj ≅ K_E.obj) ∧
      IsDerivedComplete D.l (ULift.{u} E.val) (D.geometricCurve C₀) K₀.obj ∧
      ClassicalAdic.ScalarComparisons
        (ClassicalAdic.integralToField D.l E ≫
          Profinite.padicSubfieldRingObjToPadicAlgCl D.l E) c K₀.obj
        (((WeilConjectures.condensedWeilForget (Profinite.padicAlgClRingObj D.l)
          (D.adicFrobenius C₀ hC).hom).obj K).obj) ∧
      (∀ n : ℕ, ClassicalAdic.ScalarComparisons
        (DerivedNakayama.reductionRing D.l (ULift.{u} E.val) (n + 1)) c K₀.obj
        ((AdicCompletion.derivedReduction D.l (ULift.{u} E.val)
          (D.geometricCurve C₀) n).obj K₀.obj)) ∧
      ClassicalAdic.TowerReconstruction D E (D.geometricCurve C₀)
        (CondensedRing.condensedRingOrdinaryCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val))
          (pullback.snd (C₀ ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) K₀.obj ∧
      ClassicalAdic.TowerReconstruction D E (D.geometricCurve C₀)
        (CondensedRing.condensedRingCompactCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c) K₀.obj ∧
      ∀ n : ℕ,
        letI nf := (Padic.coefficientExtensionAbsoluteValue D.l (ULift.{u} E.val)).toNormedField
        letI : TopologicalSpace (ULift.{u} E.val) :=
          nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        ClassicalAdic.EtaleComparisons
        (Padic.coefficientExtensionRing D.l (ULift.{u} E.val) (n + 1)) c
        ((AdicCompletion.derivedReduction D.l (ULift.{u} E.val)
          (D.geometricCurve C₀) n).obj K₀.obj) := by
  sorry

end RealSheaves
