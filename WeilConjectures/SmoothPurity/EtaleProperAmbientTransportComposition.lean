/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedCompactSupportCompositionCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement

/-! # Composition of Cartesian proper ambient transports

Source: Stacks Project, more-etale.tex, Tag 0F7C, vertical pasting.
(blueprint: lem-pur-etale-proper-ambient-transport-composition).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek Functor.leftDerivedFunctor
  rightDerivedLowerStarComp

private theorem compOfEq_hom
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg h).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom ≫
        eqToHom (congrArg (fun k ↦ R((k)_*[ModuleCat.{u + 1} A])) h) := by
  subst fg
  simp only [rightDerivedLowerStarCompOfEq, eqToHom_refl, Category.comp_id]

private theorem comp_assoc
    (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfull : fg ≫ h = fgh)
    (M : DerivedCategoryModule A W) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) g h gh hgh).hom.app
        (R((f)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f gh fgh
        (by rw [← hgh, ← Category.assoc, hfg, hfull])).hom.app M =
    R((h)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg hfg).hom.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) fg h fgh hfull).hom.app M := by
  subst fg
  subst gh
  rw [Category.assoc] at hfull
  subst fgh
  simpa only [compOfEq_hom, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.comp_id, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] using congr_app (push_derived_assoc A f g h) M

end AlgebraicGeometry.Etale
