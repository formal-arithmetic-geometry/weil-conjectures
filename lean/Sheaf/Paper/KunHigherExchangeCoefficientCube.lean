/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.Paper.KunBcMapOnCohomology
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Higher exchange under a morphism of squares and coefficients

Source: Stacks Project, etale-cohomology.tex, Tags 0EYM and 0EZT, the construction of
transition maps and the final comparison, respectively
(blueprint: lem-kun-higher-exchange-coefficient-cube).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Degreewise exchange for abelian sheaves on any commutative scheme square.
This is the cohomology of the canonical bounded below derived mate, conjugated by
exact-inverse-image cohomology and inverse-image/single-complex comparisons.
No cartesian or invertibility hypothesis is used. This is the map called `P^q`, `Q^q`,
or, on a cartesian face, `β` in the node; the resolution interpretation of the latter
is `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`.
Source: Stacks Project, Tags 0EYM and 0EZT
(blueprint: lem-kun-higher-exchange-coefficient-cube). -/
noncomputable def abelianHigherExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((g)^*[AddCommGrpCat.{u + 1}]).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((g')^*[AddCommGrpCat.{u + 1}]).obj F))) :=
  (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The higher exchange square commutes for an arbitrary coefficient morphism.
The initial inverse of `squareUpperStarIso sqf` identifies `x⁻¹ f₀⁻¹` with `f₁⁻¹ s⁻¹`.
The final inverse of `squareUpperStarIso sqe` is `χ : y⁻¹ e₀⁻¹ ≅ e₁⁻¹ a⁻¹`.
Functor composition with `singleFunctor`, derived direct image, and `homologyFunctor`
is exactly `R^q` on coefficient morphisms. Thus the left path is `β₁ ∘ Uφ`, and the
right path is `Vφ ∘ x⁻¹β₀`.

Proof (the four steps of the node):
1. Put `K₀ = F₀[0]`, `K₁ = F₁[0]`. The single-complex comparison turns `φ` into
   `a⁻¹K₀ ⟶ K₁`. Apply lem-kun-derived-exchange-cube to the six commuting faces
   and `K₀`, inserting the canonical inverse-image composition comparisons.
2. Use naturality of def-kun-commutative-derived-exchange at this coefficient map.
   Precompose with the comparison-face exchange and substitute the derived cube
   identity from step 1. Associativity gives the desired derived equality.
3. Apply lem-weil-pbc-exact-functor-complex-cohomology to inverse images. Descend
   its natural comparisons through lem-weil-pbc-localization-universal-property,
   clauses (2) and (3). The termwise description in
   lem-weil-pbc-derived-inverse-image-composition identifies their composition
   comparisons with the ordinary sheaf comparisons, including `χ`.
4. Apply degree-`q` cohomology. def-weil-pbc-direct-image identifies the resulting
   functors and their maps with `R^q`. On the two cartesian faces, the canonical
   commutative-square comparison and def-weil-pbc-derived-square-iso have the same
   termwise composite and hence the same derived class by localization. Their mates
   agree with def-weil-pbc-derived-exchange. Consequently lem-kun-bc-map-on-cohomology
   identifies the two remaining factors with the usual higher base-change maps.
   The other factors are precisely the displayed coefficient maps and `χ`.
Neither the coefficient map nor the comparison exchanges are inverted.
Source: Stacks Project, Tags 0EYM and 0EZT
(blueprint: lem-kun-higher-exchange-coefficient-cube). -/
theorem abelianHigherExchange_coefficient_cube
    {X₀ Y₀ S₀ T₀ X₁ Y₁ S₁ T₁ : Scheme.{u}}
    {h₀ : Y₀ ⟶ X₀} {e₀ : Y₀ ⟶ T₀} {f₀ : X₀ ⟶ S₀} {g₀ : T₀ ⟶ S₀}
    {h₁ : Y₁ ⟶ X₁} {e₁ : Y₁ ⟶ T₁} {f₁ : X₁ ⟶ S₁} {g₁ : T₁ ⟶ S₁}
    {x : X₁ ⟶ X₀} {y : Y₁ ⟶ Y₀} {s : S₁ ⟶ S₀} {a : T₁ ⟶ T₀}
    (sq₀ : ChosenCartesianSquare e₀ h₀ g₀ f₀)
    (sq₁ : ChosenCartesianSquare e₁ h₁ g₁ f₁)
    (sqf : CommSq x f₁ f₀ s) (sqg : CommSq a g₁ g₀ s)
    (sqh : CommSq y h₁ h₀ x) (sqe : CommSq y e₁ e₀ a)
    (F₀ : Sheaf T₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf T₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁) (q : ℕ) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sqf).inv.app
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F₀))) ≫
    ((f₁)^*[AddCommGrpCat.{u + 1}]).map
      (abelianHigherExchange sqg F₀ q ≫
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (g₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map φ) ≫
    abelianHigherExchange sq₁.toCommSq F₁ q =
    ((x)^*[AddCommGrpCat.{u + 1}]).map (abelianHigherExchange sq₀.toCommSq F₀ q) ≫
    abelianHigherExchange sqh (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀) q ≫
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (h₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((squareUpperStarIso AddCommGrpCat.{u + 1} sqe).inv.app F₀ ≫
        ((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) := by
  sorry

end AlgebraicGeometry.Etale
