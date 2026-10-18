/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Composition of base change for unbounded module exchange

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-radicial-exchange-descent, proof, compatibility with composition;
main-20261015, sec-six-functors-basics, the same proof;
Stacks Project, Tags 07A7 and 0E46
(blueprint: lem-fin-module-exchange-composite-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The module inverse-image composition isomorphism `c^Λ_{a,b}` of the node.
It is the inverse of `upperStarComp`, applied termwise and descended to the unbounded
localizations, with `mapDerivedCategoryCompIso` identifying the two termwise functors.
Thus its direction is `b⁻¹ a⁻¹ ≅ (b ≫ a)⁻¹`.
Source: blueprint, lem-fin-radicial-exchange-descent, composition compatibility;
Stacks Project, Tag 07A7 (blueprint: lem-fin-module-exchange-composite-base-change). -/
noncomputable def moduleInverseImageCompIso
    (Λ : Type (u + 1)) [CommRing Λ] {U V W : Scheme.{u}}
    (a : V ⟶ W) (b : U ⟶ V) :
    D(upperStar (ModuleCat.{u + 1} Λ) a) ⋙ D(upperStar (ModuleCat.{u + 1} Λ) b) ≅
      D(upperStar (ModuleCat.{u + 1} Λ) (b ≫ a)) :=
  (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) b a) ≪≫
    Functor.mapDerivedCategoryCompIso _ _).symm

/-- Horizontal pasting for the canonical unbounded module exchange, together with its
componentwise isomorphism criterion. The two given squares are Cartesian with chosen
pullback identifications; their outer rectangle is the horizontal composite of their
underlying commutative squares. The comparison maps are exactly `c^Λ` above.
Source: blueprint, lem-fin-radicial-exchange-descent, composition compatibility;
Stacks Project, Tags 07A7 and 0E46
(blueprint: lem-fin-module-exchange-composite-base-change).

Proof: On module sheaves the inverse-image square comparison for the pasted rectangle
is the composite of the two comparisons, conjugated by the composition isomorphisms
`upperStarComp`. Apply these isomorphisms termwise to complexes. Naturality makes them
cochain maps, and exactness preserves quasi-isomorphisms, so localization descends the
same pasting identity, using `mapDerivedCategoryCompIso`. Take mates under the canonical
derived adjunctions for f, f₁ and f₂. Horizontal composition of mates identifies the mate
of this pasted comparison with the two exchanges, whiskered by inverse image on the
left and on the right. The two outside comparisons give precisely the inverse of
`c^Λ_{g,k}` and `c^Λ_{g₁,k₁}` in the formula. This proves equality of natural
transformations, not just equality on objects. Evaluating at K gives the displayed
four-arrow composite. Its outside arrows are isomorphisms, also after applying Rf₂*,
so cancelling them proves the equivalence of isomorphism assertions. The outer square
is Cartesian by pullback pasting, although the mate identity itself only uses its
underlying commutative square. -/
theorem moduleExchange_composite_baseChange
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X₁ X₂ Y Y₁ Y₂ : Scheme.{u}}
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {g : Y₁ ⟶ Y} {g₁ : X₁ ⟶ X} {k : Y₂ ⟶ Y₁} {k₁ : X₂ ⟶ X₁}
    (sq₁ : ChosenCartesianSquare g₁ f₁ f g)
    (sq₂ : ChosenCartesianSquare k₁ f₂ f₁ k) :
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (sq₂.toCommSq.horiz_comp sq₁.toCommSq) =
      Functor.whiskerLeft R(lowerStar (ModuleCat.{u + 1} Λ) f)
          (moduleInverseImageCompIso Λ g k).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq)
          D(upperStar (ModuleCat.{u + 1} Λ) k) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D(upperStar (ModuleCat.{u + 1} Λ) g₁)
          (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂.toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleInverseImageCompIso Λ g₁ k₁).hom
          R(lowerStar (ModuleCat.{u + 1} Λ) f₂)) ∧
    ∀ K : DerivedCategoryModule Λ X,
      IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (sq₂.toCommSq.horiz_comp sq₁.toCommSq)).app K) ↔
        IsIso (D(upperStar (ModuleCat.{u + 1} Λ) k).map
            ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app K) ≫
          (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂.toCommSq).app
            (D(upperStar (ModuleCat.{u + 1} Λ) g₁).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
