/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Derived extension-by-zero base change

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
cor-cbc-derived-extension-zero-base-change; Stacks Tags 03S6, 0F70 and 015F
(blueprint: cor-cbc-derived-extension-zero-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The inverse of the canonical adjunction mate, applied termwise and localized,
restricted to bounded below derived categories. Source: Stacks 03S6, 015F
(blueprint: cor-cbc-derived-extension-zero-base-change).
The `IsPullback` argument is the property underlying `OpenImmersionSquare`;
its chosen pullback identification does not affect this canonical map. -/
noncomputable def extensionZeroBaseChangeDerivedPlusIso
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((gU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq)).symm ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical composition comparison for exact extension by zero on `D⁺`.
Source: Stacks 03D8 and 015F, obtained by localizing `openImmersionLowerShriekComp`
(blueprint: cor-cbc-derived-extension-zero-base-change). -/
noncomputable def extensionZeroCompDerivedPlusIso
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    ((k)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((k ≫ j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).symm

/-- Derived extension-by-zero base change is invertible, natural, unital and compatible
with pasting in both directions. Source: blueprint cor-cbc-derived-extension-zero-base-change,
Stacks 03S6, 0F70, 015F (blueprint: cor-cbc-derived-extension-zero-base-change).

Proof plan: (1) Inverse image and extension by zero are additive exact functors
(prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-extension-by-zero-exact).
Their termwise functors preserve quasi-isomorphisms and cohomological lower bounds
(lem-weil-pbc-exact-functor-derived-factorization,
lem-weil-pbc-exact-functor-bounded-below), so all four functors act on D⁺.
(2) The underived exchange is the inverse of the mate of the unit and square
identification (lem-cbc-extension-zero-base-change,
def-weil-pbc-etale-shriek-base-change-map,
lem-weil-pbc-etale-shriek-base-change-modules). Its restriction is the identity by
lem-weil-pbc-extension-by-zero-adjunction and lem-weil-pbc-extension-by-zero-unit-iso.
The module-linear inverse-image comparisons are those of
lem-weil-pbc-inverse-image-composition-module-linear.
(3) Transpose the identity comparison under the extension-by-zero adjunction to get
the unit. For two successive base changes the transposes of the two inverse maps
coincide by naturality and associativity of inverse image
(lem-weil-pbc-derived-inverse-image-composition). Injectivity of the adjunction
bijection proves equality. For composable opens use the unit-compatible comparison
of left adjoints (lem-cbc-extension-zero-composition,
lem-weil-pbc-conjugate-iso-unit-equation, def-weil-pbc-composite-adjunction);
restriction gives identities and transposing the inverses again proves equality.
(4) Apply the sheaf exchange degreewise: naturality with the differentials gives
an isomorphism of complexes. Descend it through localization
(lem-weil-pbc-localization-universal-property), using the factorization comparisons
for each composite. This is precisely `extensionZeroBaseChangeDerivedPlusIso`.
(5) Localize the identity and both pasting equations degreewise. Localization
preserves their compositions; equality is detected on localized complexes by the
same universal property. Restrict to D⁺ to obtain the equations below. -/
theorem derivedExtensionZeroBaseChange [Finite Λ] :
    (∀ {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
      {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : IsPullback gU j' j g),
      (∀ K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K)) ∧
      (∀ (K L : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
            (t : K ⟶ L),
        (((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙ ((g)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus).map t ≫
            (extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app L =
          (extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K ≫
            (((gU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙ ((j')_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus).map t)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (IsPullback.id_horiz j)).hom.app K ≫
          ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map ((upperStarIdDerivedPlus
            (ModuleCat.{u + 1} Λ) U).hom.app K) =
        (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app (((j)_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {U' U X' X U'' X'' : Scheme.{u}}
      {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      {hU : U'' ⟶ U'} {j'' : U'' ⟶ X''} {h : X'' ⟶ X'}
      [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
      (sq : IsPullback gU j' j g) (sq' : IsPullback hU j'' j' h)
      (K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (sq'.paste_horiz sq)).hom.app K =
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h g).hom.app (((j)_!open[ModuleCat.{u +
            1} Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K) ≫
          (extensionZeroBaseChangeDerivedPlusIso Λ sq').hom.app (((gU)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((j'')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) hU gU).inv.app K)) ∧
    (∀ {V' V U' U X' X : Scheme.{u}}
      {gV : V' ⟶ V} {k' : V' ⟶ U'} {k : V ⟶ U} {gU : U' ⟶ U}
      {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      [IsOpenImmersion k] [IsOpenImmersion k']
      [IsOpenImmersion j] [IsOpenImmersion j']
      (sqk : IsPullback gV k' k gU) (sqj : IsPullback gU j' j g)
      (K : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (sqk.paste_vert sqj)).hom.app K =
        ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map ((extensionZeroCompDerivedPlusIso
            Λ k j).inv.app K) ≫
          (extensionZeroBaseChangeDerivedPlusIso Λ sqj).hom.app (((k)_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((extensionZeroBaseChangeDerivedPlusIso Λ sqk).hom.app K) ≫
          (extensionZeroCompDerivedPlusIso Λ k' j').hom.app (((gV)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
