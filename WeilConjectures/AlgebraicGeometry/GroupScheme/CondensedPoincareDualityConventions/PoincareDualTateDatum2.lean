/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory

/-! # Dual and Tate data in the condensed Poincare conventions

Source: latest blueprint, sec-smooth-purity/sk-def-sf-weil-complexes/
def-pod-dual-tate-datum.md (blueprint: def-pod-dual-tate-datum).

The three-arrow dual and inverse-tensorator twisted dual reuse the recorded strict-Weil
constructions. The final statements record the constant-unit normalization and its
ordinary and compact-support global Frobenius iterates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

private theorem unit_inverse {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (X : C) :
    (unitNatIso.app X).inv = (λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app X := by
  apply (cancel_epi (unitNatIso.app X).hom).1
  rw [Iso.hom_inv_id, leftUnitor_inv_naturality_assoc,
    Iso.app_hom, whiskerLeft_unitNatIso_hom_app_ihom_ev_app]
  change 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom
  simp

private theorem unit_dual {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] :
    ((Functor.Monoidal.ihomObjIso F (𝟙_ C) (𝟙_ C) ≪≫
      (ihom (F.obj (𝟙_ C))).mapIso (Functor.Monoidal.εIso F).symm ≪≫
      (internalHom.mapIso (Functor.Monoidal.εIso F).op).app (𝟙_ C)).hom) ≫
        (unitNatIso.app (𝟙_ C)).inv =
      F.map (unitNatIso.app (𝟙_ C)).inv ≫ (Functor.Monoidal.εIso F).inv := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.Monoidal.ihomObjIso_hom]
  change ((Functor.LaxMonoidal.ihomComparison F (𝟙_ C)).natTrans.app (𝟙_ C) ≫
    (ihom (F.obj (𝟙_ C))).map (Functor.Monoidal.εIso F).inv ≫
    (pre (Functor.Monoidal.εIso F).hom).app (𝟙_ C)) ≫ _ = _
  rw [unit_inverse, leftUnitor_inv_naturality_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [id_tensor_pre_app_comp_ev, whisker_exchange_assoc,
    ihom.ev_naturality, whisker_exchange_assoc,
    Functor.LaxMonoidal.ihomComparison_ev_assoc]
  simp only [Functor.Monoidal.εIso_hom, Functor.comp_obj]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
  simp only [Functor.map_comp, Category.assoc]


namespace WeilConjectures.CondensedPoincareDualityConventions

variable (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)

set_option quotPrecheck false

local notation "Λ" => (P.presentation c).obj P.ell
local notation "g" =>
  (show P.X ≅ P.X from
    ⟨(P.datum.geometricFrobenius P.X₀).hom, (P.datum.geometricFrobenius P.X₀).inv,
      (P.datum.geometricFrobenius P.X₀).hom_inv_id,
      (P.datum.geometricFrobenius P.X₀).inv_hom_id⟩)

/-- The canonical identification [1,1] = 1 intertwines the two Weil data.
Source: the constant-unit sentence (blueprint: def-pod-dual-tate-datum).
Proof: write a for the inverse monoidal unit map and d for the three-arrow dual
structure. The evaluation identity of the closed comparison and naturality in both
Hom slots give ev (1 tensor d) = a P(ev) mu (a^-1 tensor 1). Precompose with the
inverse left unitor. The monoidal left-unit equation identifies the last two
factors with P(lambda^-1), giving u d = a P(u). Here u is exactly the inverse
unitNatIso, so this is the stated equation, with no choice of a unit identification. -/
theorem constantDual_datum :
    (P.constantDualWeil c).str.hom.hom ≫
        (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv =
      (StrictWeilCondensed.action Λ g).map
          (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv ≫
        (P.constantUnitWeil c).str.hom.hom := by
  have hunit : (ObjectProperty.ι _).mapIso (P.constantUnitWeil c).str =
      (Functor.Monoidal.εIso (StrictWeilCondensed.action Λ g)).symm := by
    ext
    simp [constantUnitWeil]
  simp only [constantDualWeil, StrictWeilCondensed.dualComplex,
    Endofunctor.IsoAlgebra.mk_str, ObjectProperty.isoMk, ObjectProperty.homMk_hom]
  rw [hunit]
  simpa [constantUnitWeil, StrictWeilCondensed.dualDatum] using
    unit_dual (StrictWeilCondensed.action Λ g)


end WeilConjectures.CondensedPoincareDualityConventions
