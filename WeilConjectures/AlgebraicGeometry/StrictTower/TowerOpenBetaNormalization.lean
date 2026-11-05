/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerSquareUnitSections
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-!
# Open-unit normalization of base change on strict constant towers

Source: Stacks Project, Tags 09AE and 04J0; the final coherence sentence of
`thm-cbc-complete-proetale.proof.md`, main-20261015
(blueprint: lem-cbc-tower-open-beta-normalization).

All derived categories are ordinary unbounded derived categories of strict diagrams.
The natural transformations are compared before any derived evaluation is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The specified module inverse-image/direct-image adjunction, without new choices.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⊣ moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)

set_option backward.isDefEq.respectTransparency false in
private theorem openBetaModuleJUnit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
    (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A j) (fixedOpen B j)

/-- The specified inverse open-unit transpose is invertible for arbitrary constant B.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: conjugate the section-normalized right-adjoint comparison under the composite
adjunctions (def-weil-pbc-composite-adjunction,
lem-weil-pbc-conjugate-iso-unit-equation). The iterated-mate formula
lem-trf-iterated-square-mates identifies its inverse with `singleBetaInv`.
The transpose formula lem-pur-adjunction-mate-transpose gives precisely the pulled-back
open unit, so injectivity of the Hom equivalence proves the identification. -/
theorem openBetaModule_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g w) := by
  have := openBetaModuleJUnit B j
  have := openBetaModuleJUnit B j'
  let fm := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := fm.full
  have := fm.faithful
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g w).app M) := by
    have : IsIso ((moduleJAdj B j').counit.app
        ((modulePullback B g).obj ((moduleJ B j).obj M))) :=
      (moduleJAdj B j').isIso_counit_app_of_iso ((moduleOpenSquare B a j' j g sq).app M)
    change IsIso (singleBetaInvApp B a j' j g w M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The sheaf comparison is the inverse of the prescribed open-unit transpose.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModule {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j' :=
  (@asIso _ _ _ _ (singleBetaInv B a j' j g w)
    (openBetaModule_isIso B a j' j g w sq)).symm

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] moduleGComp moduleRComp moduleSquareG modulePullback
attribute [local irreducible] constantRingIso

attribute [local irreducible] gComp gId adj jAdj G R J alpha

attribute [local semireducible] G R J adj jAdj gComp gId alpha
set_option backward.isDefEq.respectTransparency true

/-- The module open compositor conjugate to the specified inverse-image compositor.
Source: Stacks, Tags 09AE and 0DV0
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleJComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    moduleJ B j ⋙ moduleJ B k ≅ moduleJ B (j ≫ k) :=
  Adjunction.leftAdjointCompIso (moduleJAdj B j) (moduleJAdj B k)
    (moduleJAdj B (j ≫ k)) (moduleGComp B j k).symm

set_option backward.isDefEq.respectTransparency false

@[irreducible] private def moduleCompEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    modulePullback B h ≅ modulePullback B g ⋙ modulePullback B f :=
  eqToIso (congrArg (modulePullback B) w.symm) ≪≫ moduleGComp B f g

section Finite

variable [Finite B] [TopologicalSpace B] [DiscreteTopology B]

section FiniteComparisonProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] C Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleRingModulePullback upperStar upperStarLowerStarAdjunction upperStarComp
  upperStarCompIso upperStarCongr

end FiniteComparisonProof

end Finite

end AlgebraicGeometry.ProEtale.StrictTower

attribute [instance] CategoryTheory.catToReflQuiver
