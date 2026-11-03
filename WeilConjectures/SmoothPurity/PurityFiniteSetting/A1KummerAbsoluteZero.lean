/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.A1KummerEtaleData
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import Mathlib.Algebra.Polynomial.Laurent
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjunctionSingleZero
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions

/-! # The normalized degree-zero Kummer section

Source: det-prop-a1-kummer.proof.md, Degrees 0 and 1: connectedness identifies the
constant sections in degree zero. No induction on the coefficient level is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
namespace WeilConjectures.PurityFiniteSetting

private theorem normalizedGlobalSection_zero_isIso (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) [ConnectedSpace T]
    (c : kummerExchangeConstant A T ⟶ Scheme.finiteEtaleTateLine T m A hA)
    [IsIso c] : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerGlobalSection A m hA T c)) := by
  let adj := constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) 0
  let M := ModuleCat.of A A
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  obtain ⟨e, he⟩ := adj.derivedPlus_unit_homology_zero M
  have hu : IsIso (H.map
      (adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
    have : IsIso (H.map
        (adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≫
          e.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  unfold normalizedKummerGlobalSection
  rw [Adjunction.homEquiv_apply, Functor.map_comp]
  infer_instance

/-- The specified degree-zero constant-section maps on the two absolute curves are
isomorphisms, for the actual all-level coefficient quotient.
Source: det-prop-a1-kummer.proof.md, Degrees 0 and 1
(blueprint: new-pur-a1-kummer-absolute-zero).

Proof: the two curves are connected. The module constant-sheaf functor is fully
faithful on a connected scheme, so the ordinary constant/sections unit is invertible.
Degree-zero homology of its derived unit is this ordinary unit, up to the canonical
single/H0 and derived-sections comparisons. Thus the derived unit induces an
isomorphism in degree zero. The primitive-root map to the root tensor is an
isomorphism for any annihilated coefficient ring; applying derived sections and
composing with the derived unit preserves invertibility. This composite is exactly
the specified normalized global-section map. -/
theorem a1KummerAbsoluteZero_isIso (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (b : Bool) :
    IsIso (P.a1KummerAbsoluteZero ζ hζ b) := by
  have : ConnectedSpace (KummerLine.curve P.field.k b) := by
    cases b <;> dsimp [KummerLine.curve] <;> infer_instance
  have := normalizedKummerConstantMap_isIso P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates hζ _ (KummerLine.structureMap P.field.k b)
  exact normalizedGlobalSection_zero_isIso P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates _ _

end WeilConjectures.PurityFiniteSetting
