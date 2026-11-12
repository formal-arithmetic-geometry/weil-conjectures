/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# Identity and pasting for the derived base change map

The three laws for the derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` on bounded below derived categories of
étale sheaves, bundled into one statement (blueprint `lemma-identity-pasting`): it is the
identity for an identity square (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`), and
it is compatible with horizontal (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`)
and vertical (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert`) pasting of
commutative squares.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

/-- Blueprint `lemma-identity-pasting`: **identity and pasting** for the derived base change
map. The base change map of an identity square is the identity (modulo the identity
isomorphisms of the derived pullbacks), and the base change map of a horizontally or vertically
pasted square is the composite of the base change maps of the two squares (modulo the
composition isomorphisms of the derived pullbacks, resp. direct images). Only commutativity of
the squares is required. -/
theorem Etale.derivedBaseChangeMapPlus_id_and_paste :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)),
      Etale.derivedBaseChangeMapPlus A sq =
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (Etale.upperStarIdDerivedPlus A Y).hom ≫
          (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (Etale.upperStarIdDerivedPlus A X).inv
            (f)_*[A].rightDerivedFunctorPlus) ∧
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
      {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)),
      Etale.derivedBaseChangeMapPlus A sq =
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (Etale.upperStarCompDerivedPlus A h g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
            ((h)^*[A]).mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
            (Etale.derivedBaseChangeMapPlus A sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').inv
            (f'')_*[A].rightDerivedFunctorPlus) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k),
      Etale.derivedBaseChangeMapPlus A sq =
        Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
            (Etale.lowerStarComp A f e)).inv ((k)^*[A]).mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (Etale.derivedBaseChangeMapPlus A sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
            (e')_*[A].rightDerivedFunctorPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
            (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
              (Etale.lowerStarComp A f' e')).hom) :=
  ⟨fun f sq ↦ Etale.derivedBaseChangeMapPlus_id A f sq,
    fun sq₁ sq₂ sq ↦ Etale.derivedBaseChangeMapPlus_paste_horiz A sq₁ sq₂ sq,
    fun sq₁ sq₂ sq ↦ Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq⟩

end AlgebraicGeometry
