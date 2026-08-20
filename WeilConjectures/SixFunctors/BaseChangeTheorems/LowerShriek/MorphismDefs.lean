/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Derived
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# The base-change morphism for the lower shriek

Fix a Cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y`
of `f`. This file constructs the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` (in diagrammatic `⋙`-order)

on the bounded below derived categories of étale sheaves, where `c' = c.baseChange sq`
is the base-changed compactification of `f'` and `Rf_!^c := i_! ⋙ Rp_*` is the derived
lower shriek associated with `c` — the bounded below derived incarnation of the lower
shriek `Compactification.lowerShriek` (`f_!^c = i_! ⋙ p_*`), in which the exact
extension by zero `i_!` needs no resolutions and only the pushforward is derived.

Following the construction of the reference (see `reference.tex` in this directory),
`Ex_!^c` is assembled from two exchange morphisms:

- the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper
  square of the base-changed compactification, which is the base-change morphism
  `Etale.baseChange` of `WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`
  (no properness enters its construction);
- the *extension-by-zero exchange* for the open-immersion square of the base-changed
  compactification. Its canonical mate goes in the direction
  `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` (`Etale.openImmersionShriekBaseChange`); base change
  for extension by zero asserts that this mate is an isomorphism
  (`Etale.isIso_openImmersionShriekBaseChange`, currently `sorry`: on geometric stalks
  both sides are the pulled-back stalk on `X'` and vanish outside `X'`), and the
  construction of `Ex_!^c` uses its inverse, as in the reference.

The independence of `Ex_!^c` from the chosen compactification (Section 4 of the
reference) is *not* treated here; all statements are relative to an explicit
compactification `c`.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSquareComparison`: the pullback comparison of a
  commutative square on the underived étale sheaf categories.
- `AlgebraicGeometry.Etale.openImmersionShriekBaseChange`: the canonical exchange
  morphism `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` for a square of open immersions, with
  `Etale.isIso_openImmersionShriekBaseChange` (base change for extension by zero) and
  its bounded below derived form `Etale.openImmersionShriekBaseChangePlus`.
- `AlgebraicGeometry.Compactification.rightDerivedLowerShriekPlus`: the derived lower
  shriek `Rf_!^c = i_! ⋙ Rp_*` of a compactification on the bounded below derived
  categories.
- `AlgebraicGeometry.Etale.lowerShriekBaseChange`: the compact-support base-change
  morphism `Ex_!^c`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

/-! ### The extension-by-zero exchange morphism on underived sheaf categories -/

section OpenImmersionExchange

/- For a Grothendieck abelian coefficient category `A` the pullback functors
`Etale.upperStar` along arbitrary morphisms and the extensions by zero along open
immersions are available without further hypotheses: sheafification and the pointwise
left Kan extensions for the small étale sites are provided by the instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian`. -/
variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]

section SquareComparison

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : f'^* ∘ g^* ≅ g'^* ∘ f^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the underived étale sheaf categories, obtained from the
composition isomorphisms `Etale.upperStarComp` and the commutativity of the square. This
is the underived form of `Etale.pullbackSquareComparison`. -/
noncomputable def Etale.upperStarSquareComparison (sq : CommSq g' f' f g) :
    Etale.upperStar A g ⋙ Etale.upperStar A f' ≅
      Etale.upperStar A f ⋙ Etale.upperStar A g' :=
  (Etale.upperStarComp A f' g).symm ≪≫ eqToIso (by rw [← sq.w]) ≪≫
    Etale.upperStarComp A g' f

end SquareComparison

section OpenImmersionSquare

variable {X Z X' Z' : Scheme.{u}}
  {j : X ⟶ Z} {ρ : Z' ⟶ Z} {j' : X' ⟶ Z'} {ρ' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The canonical exchange morphism `ρ'^* ⋙ j'_! ⟶ j_! ⋙ ρ^*` for a commutative square

```
X' --ρ'--> X
|          |
j'         j
v          v
Z' --ρ---> Z
```

of schemes with `j` and `j'` open immersions, on the underived étale sheaf categories:
the mate of the pullback comparison `Etale.upperStarSquareComparison` with respect to
the adjunctions `j_! ⊣ j^*` and `j'_! ⊣ j'^*` — insert the unit of `j_! ⊣ j^*`,
transport along the pullback comparison of the square, and contract with the counit of
`j'_! ⊣ j'^*`.

Note the direction: the mate calculus produces a morphism *out of* the extension by
zero of the pullback; for a *Cartesian* square it is an isomorphism, see
`Etale.isIso_openImmersionShriekBaseChange`. -/
noncomputable def Etale.openImmersionShriekBaseChange (sq : CommSq ρ' j' j ρ) :
    Etale.upperStar A ρ' ⋙ Etale.openImmersionLowerShriek A j' ⟶
      Etale.openImmersionLowerShriek A j ⋙ Etale.upperStar A ρ :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit
      (Etale.upperStar A ρ' ⋙ Etale.openImmersionLowerShriek A j') ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.openImmersionLowerShriek A j)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.upperStarSquareComparison A sq.flip).hom
          (Etale.openImmersionLowerShriek A j') ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Etale.upperStar A ρ)
          (Etale.openImmersionLowerShriekUpperStarAdjunction A j').counit ≫
        (Functor.rightUnitor _).hom)

/-- **Base change for extension by zero**: for a *Cartesian* square with `j` and `j'`
open immersions, the exchange morphism `ρ'^* ⋙ j'_! ⟶ j_! ⋙ ρ^*` is an isomorphism.

Mathematically, since the square is Cartesian, `X'` is the preimage of the open
subscheme `X ⊆ Z` under `ρ`, and on geometric stalks both sides are the pulled-back
stalk at points of `X'` and vanish outside `X'`. -/
theorem Etale.isIso_openImmersionShriekBaseChange (sq : IsPullback ρ' j' j ρ) :
    IsIso (Etale.openImmersionShriekBaseChange A sq.toCommSq) :=
  sorry

end OpenImmersionSquare

end OpenImmersionExchange

/-! ### The derived lower shriek of a compactification and the base-change morphism -/

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

/- Sheafification and pointwise left Kan extensions for the small étale sites of all
schemes at once, following the convention of
`WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`. The localized derived
categories are the chosen `Scheme.hasDerivedCategory_sheaf_smallEtaleTopology` instances
of `WeilConjectures.SixFunctors.Derived`. -/
variable [∀ (T : Scheme.{u}), HasSheafify T.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S),
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ φ).op.lan :
      (S.Etaleᵒᵖ ⥤ A) ⥤ T.Etaleᵒᵖ ⥤ A)]

/- The K-flat resolution package on the coefficient category `A`, entering through the
derived adjunctions used by the direct-image exchange `Etale.baseChange`, as in
`WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section OpenImmersionSquarePlus

variable {X Z X' Z' : Scheme.{u}}
  {j : X ⟶ Z} {ρ : Z' ⟶ Z} {j' : X' ⟶ Z'} {ρ' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The extension-by-zero exchange isomorphism of a Cartesian square with `j` and `j'`
open immersions on the bounded below derived categories,

`Lρ'^* ⋙ j'_! ≅ j_! ⋙ Lρ^*`,

obtained from the underived exchange isomorphism by the functoriality of
`Functor.mapDerivedCategoryPlus`: all four functors are exact, so no resolutions
enter. -/
noncomputable def Etale.openImmersionShriekBaseChangePlus (sq : IsPullback ρ' j' j ρ) :
    (Etale.upperStar A ρ').mapDerivedCategoryPlus ⋙
        (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A ρ).mapDerivedCategoryPlus :=
  have := Etale.isIso_openImmersionShriekBaseChange A sq
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (Etale.openImmersionShriekBaseChange A sq.toCommSq)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

end OpenImmersionSquarePlus

section DerivedLowerShriek

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The derived lower shriek `Rf_!^c : D^+(X_ét) ⥤ D^+(Y_ét)` associated with a
compactification `c : X ⟶[i] Z ⟶[p] Y` of `f` on the bounded below derived categories
of étale sheaves: the extension by zero `i_!` applied levelwise (it is exact, so no
resolutions are needed), followed by the right derived pushforward `Rp_*`.

This is the bounded below derived incarnation of the lower shriek
`Compactification.lowerShriek` (`f_!^c = i_! ⋙ p_*`) associated with `c`, following
the definition `Rf_! K := Rp_* i_! K` of the reference; it depends on the chosen
compactification, the comparison between different choices being the independence-of-
compactification theorem, which is not treated here. -/
noncomputable def Compactification.rightDerivedLowerShriekPlus (c : Compactification f) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctorPlus

end DerivedLowerShriek

section LowerShriekBaseChange

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support base-change morphism*
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of a Cartesian square
`sq : IsPullback g' f' f g` for a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, where
`c' = c.baseChange sq` is the base-changed compactification of `f'`, on the bounded
below derived categories of étale sheaves.

Following the reference, it is the composite of the direct-image exchange
`Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` (`Etale.baseChange`) for the proper square of
the base-changed compactification, whiskered with `i_!`, and the inverse of the
extension-by-zero exchange isomorphism `Lg'^* ⋙ i'_! ≅ i_! ⋙ Lḡ^*`
(`Etale.openImmersionShriekBaseChangePlus`) for its open-immersion square, whiskered
with `Rp'_*`.

Proper base change asserts that this morphism is an isomorphism (the direct-image
exchange is one by proper base change for the proper morphism `p`); no such assertion is
built into the definition. -/
noncomputable def Etale.lowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    c.rightDerivedLowerShriekPlus A ⋙ (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
      (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (c.baseChange sq).rightDerivedLowerShriekPlus A :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus
      (Etale.baseChange A (c.baseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Etale.openImmersionShriekBaseChangePlus A (c.baseChange_isPullback_i sq)).inv
      ((Etale.lowerStar A (c.baseChange sq).g).rightDerivedFunctorPlus) ≫
    (Functor.associator _ _ _).hom

end LowerShriekBaseChange

end AlgebraicGeometry
