/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Mathlib.Algebra.Polynomial.Laurent
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Etale cohomology inputs for the finite-level affine-line computation
Source: det-prop-a1-kummer.proof.md, strict-local reduction and coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
namespace WeilConjectures.PurityFiniteSetting

/-- The absolute numerical calculation and its specified unit and Kummer basis.
Source: det-prop-a1-kummer.proof.md, coefficients and degrees zero and one
(blueprint: def-pur-a1-kummer-etale-data). -/
def A1KummerAbsoluteConclusions (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) : Prop :=
  (∀ b : Bool, IsIso (P.a1KummerAbsoluteZero ζ hζ b)) ∧
  IsIso P.a1KummerAbsoluteGenerator ∧
  ∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q → IsZero
    ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj (P.a1KummerAbsoluteImage b))

/-- The relative etale calculation before the canonical site and scheme comparisons.
Source: det-prop-a1-kummer, strict-local reduction (blueprint: def-pur-a1-kummer-etale-data). -/
def A1KummerEtaleConclusions (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of P.field.k)) : Prop :=
  (∀ b : Bool, IsIso (P.a1KummerEtaleZero ζ hζ a b)) ∧
  IsIso (P.a1KummerEtaleGenerator a) ∧
  ∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q → IsZero
    ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj (P.a1KummerEtaleImage a b))

end WeilConjectures.PurityFiniteSetting
