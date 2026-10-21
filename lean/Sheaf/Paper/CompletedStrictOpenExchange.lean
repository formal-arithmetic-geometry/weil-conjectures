/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CompletedExtensionZeroComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Strict open exchange over completed coefficient rings

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before Rlim;
Stacks Project, Tags 03DI, 03DJ, 04J0 and 06XN.
(blueprint: def-cbc-completed-strict-open-exchange).

All tower operations precede derived inverse limits. The ordinary inverse exchange
is the already specified adjoint conjugate of the sectionwise cartesian comparison.
Its strict lift and its derived descent retain that normalization. Positive level
n+1 is encoded by n : ℕ. No completeness or quasi-compactness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint


variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Termwise sheafified open extension on actual completed-ring towers.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictOpenModule {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j) :
    pbcTowers U (pbcAdicCompletion U d) ⥤ pbcTowers X (pbcAdicCompletion X d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcOpenShriek d j hj)

/-- Additivity is checked at every tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: extension presheaves, sheafification and slice transport are additive;
apply their sum equation to each component of a tower morphism. -/
@[instance] theorem cbcStrictOpenModule_additive {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) : (cbcStrictOpenModule d j hj).Additive := by
  sorry

/-- Exactness of extension on towers is levelwise, with no condition on the open.
Source: Stacks 03DJ (blueprint: def-cbc-completed-strict-open-exchange).
Proof: kernels and cokernels of strict diagrams are levelwise. Exactness of
sheafified slice extension therefore preserves both finite limits and colimits. -/
@[instance] theorem cbcStrictOpenModule_limits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteLimits (cbcStrictOpenModule d j hj) := by
  sorry

/-- Finite colimits are preserved at each tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the slice extension is left adjoint to restriction, hence preserves finite
colimits. Colimits of strict diagrams are computed at each index. -/
@[instance] theorem cbcStrictOpenModule_colimits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteColimits (cbcStrictOpenModule d j hj) := by
  sorry

/-- Exact open extension on the derived category of strict towers.
Source: Stacks 03DJ (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictOpen {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j) :=
  (cbcStrictOpenModule d j hj).mapDerivedCategory

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

/-- Naturality of the fixed inverse exchange along a strict tower transition.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: apply naturality of cbcUnderivedInverseExchange to the specified tower map. -/
theorem cbcStrictInverseLevel_naturality
    (M : pbcTowers U (pbcAdicCompletion U d)) (a b : ℕᵒᵖ) (f : a ⟶ b) :
    ((completedTowerModulePullback gU d ⋙
        cbcStrictOpenModule d j' sq.isOpenImmersion').obj M).map f ≫
      (cbcUnderivedInverseExchange d sq).app (M.obj b) =
    (cbcUnderivedInverseExchange d sq).app (M.obj a) ≫
      ((cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d).obj M).map f := by
  sorry

/-- The inverse exchange as an actual map of strict towers.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictInverseComponent (M : pbcTowers U (pbcAdicCompletion U d)) :
    (completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion').obj M ⟶
    (cbcStrictOpenModule d j sq.isOpenImmersion ⋙
      completedTowerModulePullback g d).obj M where
  app n := (cbcUnderivedInverseExchange d sq).app (M.obj n)
  naturality a b f := cbcStrictInverseLevel_naturality d sq M a b f

/-- Naturality in the original strict tower.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: at every index apply ordinary inverse-exchange naturality to that component
of the tower morphism. Extensionality of natural transformations gives the result. -/
theorem cbcStrictInverseComponent_naturality
    (M N : pbcTowers U (pbcAdicCompletion U d)) (f : M ⟶ N) :
    (completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion').map f ≫
        cbcStrictInverseComponent d sq N =
    cbcStrictInverseComponent d sq M ≫
      (cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d).map f := by
  sorry

/-- Simultaneous inverse diagram map. Its component at every index is the fixed
ordinary inverse exchange, the conjugate of restriction along the cartesian map.
The forward diagram map is its inverse, already before derived localization.
Source: Stacks 03DI, 04J0 (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictInverseModule :
    completedTowerModulePullback gU d ⋙ cbcStrictOpenModule d j' sq.isOpenImmersion' ⟶
      cbcStrictOpenModule d j sq.isOpenImmersion ⋙ completedTowerModulePullback g d where
  app M := cbcStrictInverseComponent d sq M
  naturality M N f := cbcStrictInverseComponent_naturality d sq M N f

/-- The simultaneous strict maps are inverse, component by component.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the inverse at each index is the forward ordinary exchange. Naturality
makes both maps strict; their composites are identities at each index. -/
@[instance] theorem cbcStrictInverseModule_isIso : IsIso (cbcStrictInverseModule d sq) := by
  sorry

/-- The strict representative equation, using the actual universal pullback counits.
It specifies the inverse map, so also specifies its forward inverse uniquely.
Source: Stacks 06XN (blueprint: def-cbc-completed-strict-open-exchange). -/
def CbcStrictExchangeNormalization
    (b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
      completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion') : Prop :=
  ∀ P : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ,
    (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion U d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules U (pbcAdicCompletion U d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P)) →
    HEq
      (b.inv.app (DerivedCategory.Q.obj P) ≫
      (completedTowerPullback g d).map
        ((cbcStrictOpenModule d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app P) ≫
      completedTowerPullbackComplexCounit g d
        (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj P))
      ((cbcStrictOpen d j' sq.isOpenImmersion').map
      (completedTowerPullbackComplexCounit gU d P) ≫
      (cbcStrictOpenModule d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        (((cbcStrictInverseModule d sq).mapHomologicalComplex (.up ℤ)).app P))

/-- The normalized strict exchange exists uniquely.
Source: Stacks 03DI, 03DJ, 04J0, 06XN and the blueprint finite-exchange refinement
(blueprint: def-cbc-completed-strict-open-exchange).
Proof: (1) localization identifies both restricted completed rings, projection by
projection. (2) Compose open-extension and module-pullback adjunctions.
(3) Restriction along the cartesian comparison gives the right-adjoint isomorphism.
(4) Conjugation gives the already specified ordinary inverse exchange and its inverse.
(5) Apply these maps simultaneously at every index and cochain degree; naturality
commutes with all transitions and differentials. (6) Take a strict objectwise
K-flat flat-term replacement. Open extension preserves this resolving class by
the slice tensor projection formula. The two maps thus descend through the
universal left-derived counits. Their strict inverse identities descend as well.
The displayed representative equation and resolving-class universality give uniqueness. -/
theorem cbcStrictExchange_existsUnique :
    ∃! b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
        completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion',
      CbcStrictExchangeNormalization d sq b := by
  sorry

/-- The canonical strict exchange, selected by its unique representative equation.
Source: Stacks 03DI, 06XN (blueprint: def-cbc-completed-strict-open-exchange). -/
@[irreducible] def cbcStrictExchange := (cbcStrictExchange_existsUnique d sq).exists.choose

/-- The asserted natural isomorphism on reductions of arbitrary completed-ring objects.
Source: blueprint finite exchange before Rlim
(blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcReductionStrictExchange :
    completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
        completedTowerPullback g d ≅
      completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
        cbcStrictOpen d j' sq.isOpenImmersion' :=
  Functor.isoWhiskerLeft (completedReductionTower U d) (cbcStrictExchange d sq)

end AlgebraicGeometry.Scheme
