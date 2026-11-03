/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseFlatHomSiteComparison
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteFiniteRetractDualExact
import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Data.Int.Interval
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteBoundedFreeRHomMapQuasiIso
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement

/-! # Finite projective lisse sources and bounded-below site Hom comparison

Source: blueprint, lem-weil-finite-duality-site-comparison, proof paragraph 2,
with the arbitrary finite coefficient convention of Wei Yang #1423 and the
bounded-below/projective correction of Wei Yang #1441, item 28
(blueprint: lem-sf-lisse-flat-hom-site-comparison).

The existing finite-free evaluation coordinates and two-variable naturality are reused.
The conclusion below extends the older local-coefficient, bounded-constructible theorem;
its canonical evaluation map and all earlier declarations are unchanged.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The local projective calculation for the specified map. The finite-free comparison
is expressed by the existing evaluation-coordinate assertion, for every finite-free
object T. For each retraction K -> T -> K the second clause is the actual arrow formula
beta_K = Hom(i,1) beta_T F(Hom(p,1)). In particular it applies to the maps supplied by
any splitting of a finite projective constant value into a finite free module.
Source: blueprint comparison proof, paragraph 2; Stacks 08JI and 08JJ;
Wei Yang #1441 item 28 (blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomProjectiveLocalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K N : Etale.DerivedCategoryModule A X) : Prop :=
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let H := Etale.derivedHom (ModuleCat.{u + 1} A) X
  let G := derivedHom (ModuleCat.{u + 1} A) X
  let b := siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
  (∀ T : Etale.DerivedCategoryModule A X, lisseFlatHomLocalAssertion A X T N) ∧
  (∀ (T : Etale.DerivedCategoryModule A X) (i : K ⟶ T) (p : T ⟶ K),
    i ≫ p = 𝟙 K →
    b K N = F.map ((H.map p.op).app N) ≫ b T N ≫
      (G.map (F.map i).op).app (F.obj N))

/-- Existence of finite projective constant values on an etale trivializing cover.
The displayed linear equivalence is the splitting P direct-sum Q = A^r: for two
modules the direct sum is their product. It does not assert that P itself is free.
Source: blueprint comparison proof, paragraph 2; Stacks 00NX and 08JI;
Wei Yang #1441 item 28 (blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomProjectiveCover
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ j : 𝒰.I₀,
    ∃ P Q : ModuleCat.{u + 1} A,
      Finite P ∧ Module.Projective A P ∧
      (∃ r : ℕ, Nonempty ((P × Q) ≃ₗ[A] (Fin r → A))) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (𝒰.f j)).obj L ≅
        (constantSheaf (𝒰.X j).smallEtaleTopology (ModuleCat.{u + 1} A)).obj P)

/-- Full conclusion for arbitrary finite coefficients and a bounded-below second
argument. The comparison and restriction maps are the recorded evaluation transposes.
The projective formula is quantified over every retract and the free coordinate formula
is quantified over every basis; hence it applies to every chosen splitting and change
of trivialization. Restriction squares are imposed on every slice and every successive
slice, using the same canonical internal-Hom isomorphisms.

The interval clause is conditional on constructibility of N in that interval. The
separate lower-bound clause has no constructibility or finite-Tor hypothesis.
Source: blueprint comparison proof, paragraph 2; Stacks 08JI, 08JB and 095I;
Wei Yang #1423 and #1441 item 28
(blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomGeneralSiteAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Etale.DerivedCategoryModule A X) : Prop :=
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let H := Etale.derivedHom (ModuleCat.{u + 1} A) X
  let G := derivedHom (ModuleCat.{u + 1} A) X
  let R := (H.obj (op K)).obj N
  IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K N) ∧
  lisseFlatHomNaturality H G F
    (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X) K N ∧
  lisseFlatHomProjectiveCover A X L ∧
  (∀ U : X.Etale,
    siteHomRestrictionAssertion (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)
      (siteHomEtaleRestrictionMonoidal A X U) (siteHomProEtaleRestrictionMonoidal A X U)
      K N ∧
    lisseFlatHomProjectiveLocalAssertion A U.left
      ((siteHomEtaleRestriction A X U).obj K) ((siteHomEtaleRestriction A X U).obj N) ∧
    ∀ V : U.left.Etale,
      siteHomRestrictionAssertion (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom U.left V)
        (siteHomEtaleRestrictionMonoidal A U.left V)
        (siteHomProEtaleRestrictionMonoidal A U.left V)
        ((siteHomEtaleRestriction A X U).obj K) ((siteHomEtaleRestriction A X U).obj N)) ∧
  (∀ a b : ℤ,
    (∀ j : ℤ, a ≤ j → j ≤ b → Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ j).obj N)) →
    (∀ j : ℤ, (j < a ∨ b < j) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj N)) →
    (∀ j : ℤ, a ≤ j → j ≤ b → Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ j).obj R)) ∧
    (∀ j : ℤ, (j < a ∨ b < j) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj R))) ∧
  (∀ a : ℤ, (∀ j : ℤ, j < a →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj N)) →
    ∀ j : ℤ, j < a → IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj R)) ∧
  (_root_.DerivedCategory.TStructure.t
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).plus R

end AlgebraicGeometry.ProEtale
