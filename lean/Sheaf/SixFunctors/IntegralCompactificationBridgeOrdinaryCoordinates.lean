/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
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
(blueprint: def-sf-integral-compactification-ordinary-site-transport).

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

/-- The canonical exact small-site transport on strict constant towers.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
abbrev towerModel (T : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCbcModelModules T (constantRing l E))

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_additive (T : Scheme.{u}) :
    Functor.Additive (towerModel l E T) := inferInstance

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_preservesFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (towerModel l E T) := inferInstance

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_preservesFiniteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (towerModel l E T) := inferInstance

/-- The same transport after localizing the strict diagram category.
Source: Stacks 00VC, 05RU
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
abbrev derivedTowerModel (T : Scheme.{u}) := (towerModel l E T).mapDerivedCategory

/-- Direct-image transport is uniquely fixed on every underlying section.
Source: Stacks 03D7, 00VC
(blueprint: def-sf-integral-compactification-ordinary-site-transport).
Proof: both functors are geometric precomposition with the same coefficient action.
The displayed underlying direct-image comparison is the Hom-normalized comparison of
constantSemilinearGeneratorComparison. Identity on its sections is linear, natural,
and invertible. Sections determine the comparison uniquely. -/
theorem ordinaryDirectModel_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! b : ProEtale.StrictTower.moduleDirectImage
        (ULift.{u + 1} (constantRing l E)) f ⋙ sfCbcModelModules T (constantRing l E) ≅
      sfCbcModelModules V (constantRing l E) ⋙
        (sfCbcMorphism f).modulePush (ULift.{u + 1} (constantRing l E)),
      ∀ (M : ProEtale.StrictTower.Modules (ULift.{u + 1} (constantRing l E)) V)
        (W : (proEtaleSiteModel T)ᵒᵖ)
        (x : ((sfCbcModelModules T (constantRing l E)).obj
          ((ProEtale.StrictTower.moduleDirectImage
            (ULift.{u + 1} (constantRing l E)) f).obj M)).val.obj W),
        HEq (((constantDirectUnderlying l E f).hom.app
          ((sfCbcModelModules V (constantRing l E)).obj M)).hom.app W
            ((b.hom.app M).val.app W x)) x := by
  sorry

/-- The section-normalized ordinary direct-image transport.
Source: Stacks 03D7 (blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
def ordinaryDirectModel {V T : Scheme.{u}} (f : V ⟶ T) :=
  (ordinaryDirectModel_existsUnique l E f).exists.choose

end WeilConjectures.IntegralCompactificationBridge
