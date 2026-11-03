/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunction
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteP1CoefficientSplitting
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalOrdinaryChart
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
public import WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarComposition
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarExchange
import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
import WeilConjectures.CategoryTheory.ToposFiniteFreeCompact.ToposFiniteFreeCompactConstituents

/-! # Local and global finite-free dualizing mates

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-free-extension.proof.md, paragraphs 1 and 3.
(blueprint: lem-coef-finite-free-dualizing-local-global-mate).

All categories are the ordinary unbounded small-etale derived categories. Affine space is
represented by its ordered coordinate tower, canonically isomorphic to ordinary affine
space by `affineTraceAffineSpaceIso`. The right normal form evaluated at the coefficient
unit represents the shifted Tate object, including its canonical tensor-unit identifications.
The chart coordinates below preserve counits; no independent orientation is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteFreeDualizing

/-- Canonical proper/compact-support composition, also when the two composite maps are
presented by an equality. Source: blueprint finite-free extension proof, paragraph 1,
local closed-embedding computation
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def closedLeftComparison (C : Type (u + 1)) [CommRing C] [Finite C]
    {V T S : Scheme.{u}} (i : V ⟶ T) [IsClosedImmersion i] (q : T ⟶ S)
    {g : V ⟶ S} [QuasiCompact g] (h : g = i ≫ q)
    (cq : Compactification q) (cg : Compactification g) :
    (lowerStar (ModuleCat.{u + 1} C) i).rightDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) cq ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) cg := by
  subst g
  exact Functor.isoWhiskerRight
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} C) i).symm ≪≫
        (rightDerivedLowerShriekIso C (cg.ofComp cq).restrict).symm) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso C cq (cg.ofComp cq) ≪≫
    rightDerivedLowerShriekOfCompactificationIso C (cq.comp (cg.ofComp cq)) cg

/-- Restrict the already constructed global counit mate, using scalar/restriction balancing.
Source: blueprint finite-free extension proof, paragraphs 1 and 3
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def restrictedGlobalMate
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A)
    {X S V : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (HR : DerivedCategoryModule R S ⥤ DerivedCategoryModule R X)
    (HA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X)
    (aR : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ⊣ HR)
    (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ HA)
    (v : V ⟶ X) :
    (scalarExtension φ V).obj
        ((upperStar (ModuleCat.{u + 1} R) v).mapDerivedCategory.obj
          (HR.obj (constantComplex R S))) ⟶
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj
        (HA.obj (constantComplex A S)) :=
  (finiteAffineExactPullbackScalarIso φ v).hom.app (HR.obj (constantComplex R S)) ≫
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
      (DualizingOpenMate.globalMate φ c HR HA aR aA)

end AlgebraicGeometry.Etale.FiniteFreeDualizing
