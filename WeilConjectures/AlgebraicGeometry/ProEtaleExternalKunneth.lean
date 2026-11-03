/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExternalProduct
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
public import WeilConjectures.AlgebraicGeometry.FiniteProductProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
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
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Pasting
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothBaseChangeCoefficients
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.CategoryTheory.ExactDeltaEmbeddingDetection
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Flat.FlatModel
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition

/-!
# Ordinary external Künneth on the small pro-étale site

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-sf-kunneth-star/_section.md and sk-lem-sf-kunneth-star.proof.md
(blueprint: sk-lem-sf-kunneth-star).

The maps are the adjuncts of the specified tensor products of counits. The coefficients
are ordinary finite-ring module sheaves, and the domain predicate is the recorded intrinsic
bounded constructible finite-Tor predicate. No coefficient system is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Pull back the ordinary derived counit across a commutative square.
Source: current blueprint, displayed adjunct of (1)
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethPulledCounit
    {X Y W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z} {q : Z ⟶ Y}
    (sq : CommSq p h f q)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M)) ⟶
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj M :=
  (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom.app _ ≫
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app M)

/-- The two-morphism external Künneth arrow on a pair of commuting projection squares.
It is the derived adjunction mate of the tensor product of the two pulled-back counits.
Source: current blueprint, statement and final paragraph of the proof
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethMap
    {X₁ X₂ Y₁ Y₂ W Z : Scheme.{u}}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {h : W ⟶ Z}
    {p₁ : W ⟶ X₁} {p₂ : W ⟶ X₂} {q₁ : Z ⟶ Y₁} {q₂ : Z ⟶ Y₂}
    (sq₁ : CommSq p₁ h f₁ q₁) (sq₂ : CommSq p₂ h f₂ q₂)
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) q₁).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f₁).rightDerivedFunctor.obj M₁) ⊗
      (upperStar (ModuleCat.{u + 1} A) q₂).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f₂).rightDerivedFunctor.obj M₂) ⟶
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) p₁).leftDerivedFunctor.obj M₁ ⊗
        (upperStar (ModuleCat.{u + 1} A) p₂).leftDerivedFunctor.obj M₂) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h _ _).hom ≫
      tensorHom (externalKunnethPulledCounit A sq₁ M₁)
        (externalKunnethPulledCounit A sq₂ M₂))

/-- The identity-factor arrow, with the identity on the second tensor factor.
Source: current blueprint, formula (1) and its displayed adjunct
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethIdentityMap
    {X Y T W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z}
    {q : Z ⟶ Y} {t : W ⟶ T} {s : Z ⟶ T}
    (sq : CommSq p h f q) (w : h ≫ s = t)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M) ⊗
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj Q ⟶
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj M ⊗
        (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj Q) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h _ _).hom ≫
      tensorHom (externalKunnethPulledCounit A sq M)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h s).inv.app Q ≫
          (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) w).hom.app Q))

omit [Finite A] in
end AlgebraicGeometry.ProEtale
