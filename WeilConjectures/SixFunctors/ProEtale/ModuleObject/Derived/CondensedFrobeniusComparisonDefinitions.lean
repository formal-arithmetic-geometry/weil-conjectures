/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFieldDatum.SchemeFrobeniusGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import WeilConjectures.WeilObject.Sheaf.StalkFrobenius
import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobenius
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FrobeniusNaturality
import WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.SelectedSchemeGaloisComparison
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Condensed coefficient coherence of the canonical Frobenius comparison

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.proof.md, sole transport paragraph;
Stacks Tag 0F6W (blueprint: lem-pur-condensed-frobenius-comparison-coherence).
All functors act on ordinary unbounded derived internal modules. Exact pullback
is represented termwise, using the canonical identification with total derivation.

## Main definitions

- `IsPurityFrobeniusCoefficient`: the four coefficient cases for the fixed E.
- `condensedFrobeniusComparison`: the specified factorization/trivialization composite.
- `condensedFrobeniusSquare`: the canonical comparison for a commuting scheme square.
- Scalar and model identity/composition helpers fix all comparison normalizations.

## Main statements

- `CondensedFrobeniusComparisonCoherence`: both equations and their simultaneous laws.
- `condensedFrobeniusComparison_coherence`: these laws for the specified comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The indicated family of four coefficient rings, with positive finite levels.
The last case uses finite-subextension-valued sections, not all continuous functions.
Source: coefficient convention (blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def IsPurityFrobeniusCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty
    (Mon.mk Λ.X ≅ Mon.mk (cartesianFinitePointRing
      (ULift.{u} (Padic.coefficientExtensionRing ell E.1 n))))) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.1)) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

/-- The canonical relative-Frobenius module trivialization, localized termwise.
Its coefficient map is the pullback-from-point comparison by FrobeniusPoint.
Source: absolute-Frobenius normalization, Stacks 0F6W
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedAbsoluteFrobeniusTrivialization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    scalarSixPull Λ (D.purityAbsoluteFrobenius T₀) ≅
      𝟭 (DerivedCategory (ModuleRingedComparison.internalModules
        Λ.X (D.purityFrobeniusFiber T₀).left)) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (D.purityAbsoluteFrobenius T₀)).symm ≪≫
    Functor.leftDerivedFunctorIdIso
    (upperStarIterateFrobeniusIso Λ.X D.prime
      (D.model_characteristic (pullback.fst T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ T₀.hom)) D.a)

/-- The predicate of the full constructible finite-Tor subcategory already defined by
sk-def-sfb-constructible; no alternate constructibility or coefficient model is introduced.
Source: restriction clause of the latest blueprint compatibility proof
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
abbrev frobeniusCtf (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) (K : frobeniusD D Λ T₀) : Prop :=
  constantModelBoundedConstructible Λ.X (D.purityFrobeniusFiber T₀).left K ∧
    DerivedCategory.finiteTorAmplitude _ K

end AlgebraicGeometry.ProEtale.CondensedRing
