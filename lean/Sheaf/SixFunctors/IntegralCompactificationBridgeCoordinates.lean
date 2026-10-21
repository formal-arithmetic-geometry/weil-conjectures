/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates
public import Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.SixFunctors.AmbientProperOpenPasting

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: def-sf-integral-compactification-site-transport).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary termwise direct-image square with explicit whiskering compositors.
Source: Stacks 0941 (blueprint: def-sf-integral-compactification-site-transport). -/
def towerDirectModel {V T : Scheme.{u}} (f : V ⟶ T) :
    ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f ⋙
      towerModel l E T ≅ towerModel l E V ⋙
        (sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E)) :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (ordinaryDirectModel l E f) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- The localization factorization of the exact model transport.
Source: Stacks 05RU (blueprint: def-sf-integral-compactification-site-transport). -/
def modelFactors (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ derivedTowerModel l E T ≅
      (towerModel l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (towerModel l E T).mapDerivedCategoryFactors

/-- The universal-unit normalization of a derived direct-image transport: the published
DirectSquareNormalization predicate for the termwise square towerDirectModel, with the
universal derived units and the exact-localization factorizations of the model transports.
Source: Stacks 0D6E, 0941
(blueprint: def-sf-integral-compactification-site-transport). -/
def DirectModelNormalization {V T : Scheme.{u}} (f : V ⟶ T)
    (d : ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E))) : Prop :=
  DirectSquareNormalization
    (ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E)))
    (towerModel l E V) (towerModel l E T)
    (ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)))
    (directCochainUnit
      (ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f))
    (directCochainUnit
      ((sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E))))
    (towerDirectModel l E f) d

/-- Universal-unit normalization fixes the derived direct-image transport.
Source: Stacks 0D6E, 0941
(blueprint: def-sf-integral-compactification-site-transport).
Proof: apply universal right derivation to towerDirectModel. Its universal units
satisfy the displayed cochain factorization. Uniqueness of right derivation fixes
this comparison on all complexes, and inverse exact site transport makes it invertible.
The published DirectSquareNormalization predicate, named DirectModelNormalization
here, expresses this equality using the explicit localization-factorization endpoints. -/
theorem directModel_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! d : ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)),
      DirectModelNormalization l E f d := by
  sorry

/-- The unique universal-unit-normalized derived direct-image comparison.
Source: Stacks 0D6E (blueprint: def-sf-integral-compactification-site-transport). -/
def directModel {V T : Scheme.{u}} (f : V ⟶ T) :
    ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)) :=
  (directModel_existsUnique l E f).exists.choose

/-- Pullback transport is the adjunction mate of the normalized derived direct square.
Source: Stacks 07A4 (blueprint: def-sf-integral-compactification-site-transport). -/
def pullModelMap {V T : Scheme.{u}} (f : V ⟶ T) :=
  ((mateEquiv (ProEtale.StrictTower.adj (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerAdjunction (ULift.{u + 1} (constantRing l E)))).symm
      (TwoSquare.mk _ _ _ _ (directModel l E f).hom)).natTrans

/-- Exact site equivalence makes the pullback mate invertible.
Source: Stacks 00VC, 07A4
(blueprint: def-sf-integral-compactification-site-transport).
Proof: transport the original derived adjunction through the exact site equivalences.
The normalized right comparison identifies its right adjoint. Uniqueness of left
adjoints identifies the mate with the resulting invertible pullback comparison. -/
theorem pullModelMap_isIso {V T : Scheme.{u}} (f : V ⟶ T) :
    IsIso (pullModelMap l E f) := by
  sorry

/-- The canonical pullback transport with its derived adjunction normalization.
Source: Stacks 07A4 (blueprint: def-sf-integral-compactification-site-transport). -/
def pullModel {V T : Scheme.{u}} (f : V ⟶ T) :=
  @asIso _ _ _ _ (pullModelMap l E f) (pullModelMap_isIso l E f)

/-- The inverse-direction open transport is the mate of pullModel.
Source: Stacks 03DI, 07A7
(blueprint: def-sf-integral-compactification-site-transport). -/
def openModelMap {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :=
  ((mateEquiv (ProEtale.StrictTower.jAdj (ULift.{u + 1} (constantRing l E)) j)
    (constantTowerOpenAdj l E j a)).symm
      (TwoSquare.mk _ _ _ _ (pullModel l E j).inv)).natTrans

/-- The unit-normalized open mate is invertible, including the empty open.
Source: Stacks 03DI, 03DJ
(blueprint: def-sf-integral-compactification-site-transport).
Proof: the exact small-site equivalences carry the original open adjunction to the
small-model open adjunction. Their inverse images agree by pullModel; uniqueness of
left adjoints identifies this mate with the canonical invertible comparison. -/
theorem openModelMap_isIso {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IsIso (openModelMap l E j a) := by
  sorry

/-- Open transport in the forward direction, with the same adjunction normalization.
Source: Stacks 03DI (blueprint: def-sf-integral-compactification-site-transport). -/
def openModel {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :=
  (@asIso _ _ _ _ (openModelMap l E j a) (openModelMap_isIso l E j a)).symm



end WeilConjectures.IntegralCompactificationBridge
