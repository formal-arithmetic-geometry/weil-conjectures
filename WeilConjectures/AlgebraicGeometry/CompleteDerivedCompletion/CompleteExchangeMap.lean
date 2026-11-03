/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDirectImageLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The completed exchange map

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-exchange-map.md
(blueprint: det-pbc-complete-exchange-map).

The square is only commutative. The three factors are, in order, reduction/direct-image
projection, the tower adjunction mate, and the inverse direct-image/derived-limit
comparison. All are natural transformations, so the result is natural in every K.
No properness, cartesianness or completeness assumption is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Composition of exact integral pullbacks, obtained by applying the module
composition comparison termwise to complexes and localizing.
Source: clause (1), the composition isomorphisms c
(blueprint: det-pbc-complete-exchange-map). -/
def modulePullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dpullModule l E (f ≫ g) ≅ dpullModule l E g ⋙ dpullModule l E f :=
  Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarComp (DerivedNakayama.integerRing l E) f g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g)
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)

/-- Composition of exact tower pullbacks, using the very same module comparison
levelwise before localization.
Source: clause (1), tower version (blueprint: det-pbc-complete-exchange-map). -/
def towerPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dpull l E (f ≫ g) ≅ dpull l E g ⋙ dpull l E f :=
  Functor.mapDerivedCategoryNatIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
        (CondensedRing.upperStarComp (DerivedNakayama.integerRing l E) f g)) ≪≫
    Functor.mapDerivedCategoryCompIso (pull l E g) (pull l E f)

variable {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' p' p g)

/-- The specified θ = c(g',p) c(p',g)⁻¹, using the equality of the two composite
scheme maps. Source: clause (1) (blueprint: det-pbc-complete-exchange-map). -/
def modulePullSquare : dpullModule l E g ⋙ dpullModule l E p' ≅
    dpullModule l E p ⋙ dpullModule l E g' :=
  (modulePullComp l E p' g).symm ≪≫
    eqToIso (congrArg (dpullModule l E) sq.w.symm) ≪≫ modulePullComp l E g' p

/-- The same θ on derived towers, induced levelwise from module composition.
Source: clause (1) (blueprint: det-pbc-complete-exchange-map). -/
def towerPullSquare : dpull l E g ⋙ dpull l E p' ≅ dpull l E p ⋙ dpull l E g' :=
  (towerPullComp l E p' g).symm ≪≫
    eqToIso (congrArg (dpull l E) sq.w.symm) ≪≫ towerPullComp l E g' p

/-- Ordinary exchange Ex: the unit of p', then Rp'*θ, then Rp'*g'* of the counit of p.
This is the existing mateEquiv applied to the specified comparison.
Source: clause (1), displayed formula (blueprint: det-pbc-complete-exchange-map). -/
def moduleExchange : rpushModule l E p ⋙ dpullModule l E g ⟶
    dpullModule l E g' ⋙ rpushModule l E p' :=
  (mateEquiv (moduleAdjunction l E p) (moduleAdjunction l E p')
    (.mk _ _ _ _ (modulePullSquare l E sq).hom)).natTrans

/-- Tower exchange Ex^Tow, using the same unit/comparison/counit formula on the
actual derived categories of towers. Evaluation compatibility, including units and
counits, is supplied by completeDerivedCompletion (3). Thus its n-th level is the
ordinary exchange after the canonical evaluation identifications, with transitions
already belonging to this one tower morphism.
Source: clause (1), tower version (blueprint: det-pbc-complete-exchange-map). -/
def towerExchange : rpush l E p ⋙ dpull l E g ⟶ dpull l E g' ⋙ rpush l E p' :=
  (mateEquiv (towerAdjunction l E p) (towerAdjunction l E p')
    (.mk _ _ _ _ (towerPullSquare l E sq).hom)).natTrans

/-- The completed exchange natural transformation, for every integral derived object.
First apply Rlim g*Tow to red(Rp*K) ≅ Rp*Tow red(K), then apply Rlim to Ex^Tow,
then use the inverse of Rp'*Rlim ≅ Rlim Rp'*Tow. At each positive level the ingredient
is Ex of the derived finite reduction, conjugated by the projection-formula
isomorphism. For a derived-complete K, completedPull on the right is the derived
completion of g'*K by completedPull_reduction; the definition itself is unrestricted.
Source: clause (2), displayed ordered composite and concluding paragraph
(blueprint: det-pbc-complete-exchange-map). -/
def completedExchange : rpushModule l E p ⋙ completedPull l E g ⟶
    completedPull l E g' ⋙ rpushModule l E p' :=
  Functor.whiskerRight (pushReductionIso l E p).hom (dpull l E g ⋙ rlim l E Y') ≫
    Functor.whiskerLeft (red l E X)
      (Functor.whiskerRight (towerExchange l E sq) (rlim l E Y')) ≫
    Functor.whiskerLeft (red l E X ⋙ dpull l E g') (pushLimitIso l E p').inv

/-- Ex^comp_K, the component of the specified natural completed exchange.
Source: clause (2) (blueprint: det-pbc-complete-exchange-map). -/
def completedExchangeMap (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (completedPull l E g).obj ((rpushModule l E p).obj K) ⟶
      (rpushModule l E p').obj ((completedPull l E g').obj K) :=
  (completedExchange l E sq).app K

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
