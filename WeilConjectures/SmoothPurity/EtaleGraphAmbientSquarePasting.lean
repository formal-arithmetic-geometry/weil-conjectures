/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
public import WeilConjectures.SmoothPurity.EtaleProperAmbientTransportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedCompactSupportCompositionCoherenceSupplement

/-! # Target-square subgrid of ambient projection pasting

Source: Stacks Tags 0F7C, 0F7D and 0F7J, the k-side ambient rectangle.
(blueprint: lem-pur-etale-graph-ambient-square-pasting).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp
  etaleGraphNormalizedProperOpenExchange

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
