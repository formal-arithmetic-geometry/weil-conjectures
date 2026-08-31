/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.SixFunctors.UpperLowerStar.TopologicalInvariance

/-!
# Topological invariance of étale cohomology

Étale cohomology `CategoryTheory.Sheaf.H` is by definition the `Ext`-groups out of the
constant sheaf `ℤ` on the small étale site. Any morphism of schemes `f : X ⟶ Y` therefore
induces a comparison map on étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap`): pull an `Ext`-class back along the exact functor
`f^*` and use the comparison `ℤ_X ⟶ f^* ℤ_Y` of constant sheaves
(`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`).

If `f` is a universal homeomorphism, then `f^*` is an equivalence of the small étale topoi
(`AlgebraicGeometry.Etale.isEquivalence_upperStar`), and the comparison map is an isomorphism
in every degree. This is [Stacks 03SI].

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyMap`: the comparison map
  `H^n(Y_ét, F) →+ H^n(X_ét, f^* F)` on étale cohomology along an arbitrary morphism `f`. Its
  underlying map is spelled out by `AlgebraicGeometry.Etale.cohomologyMap_apply`.
- `AlgebraicGeometry.Etale.cohomologyEquiv`: for a universal homeomorphism, the comparison
  map as an additive equivalence `H^n(Y_ét, F) ≃+ H^n(X_ét, f^* F)`.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_map`: the comparison map is natural in the sheaf,
  i.e. it commutes with `CategoryTheory.Sheaf.H.map`.
- `AlgebraicGeometry.Etale.cohomologyMap_bijective`: **topological invariance of étale
  cohomology**, [Stacks 03SI]: for a universal homeomorphism the comparison map is bijective.

## Implementation notes

The comparison map is defined for an arbitrary morphism, since nothing about universal
homeomorphisms enters its construction; only its bijectivity uses them. Bijectivity is
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` applied to `f^*`,
which is exact, fully faithful and preserves injective objects, being an equivalence, the
source topos having enough injectives, being Grothendieck abelian.

Applying `CategoryTheory.Sheaf.H` on the small étale sites needs sheafification there
(`CategoryTheory.GrothendieckTopology.hasSheafify_smallEtaleTopology`) and `Ext`-groups
(`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology`
through `CategoryTheory.IsGrothendieckAbelian.hasExt`); both are found by instance search.

## References

* [Stacks 03SI], Étale Cohomology, Proposition 59.45.4.
-/

@[expose] public section

universe u

open CategoryTheory Abelian AddCommGrpCat

namespace AlgebraicGeometry

open Scheme Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)

section ComparisonMap

/-- The comparison map on étale cohomology induced by a morphism of schemes `f : X ⟶ Y`: an
`Ext`-class out of the constant sheaf `ℤ` on the small étale site of `Y` is pulled back along
the exact functor `f^*` and then precomposed with the comparison `ℤ_X ⟶ f^* ℤ_Y` of constant
sheaves of `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`. -/
noncomputable def Etale.cohomologyMap :
    Sheaf.H F n →+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  (Ext.precompAddEquiv
      ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app (of (ULift ℤ))) _ n
    |>.toAddMonoidHom).comp
      (((f)^*[AddCommGrpCat.{u + 1}]).mapExtAddHom _ F n)

@[simp]
lemma Etale.cohomologyMap_apply (x : Sheaf.H F n) :
    Etale.cohomologyMap f F n x =
      (Ext.mk₀ ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
          (of (ULift ℤ))).hom).comp
        (x.mapExactFunctor ((f)^*[AddCommGrpCat.{u + 1}])) (zero_add n) :=
  rfl

/-- The comparison map on étale cohomology is natural in the sheaf: it commutes with the maps
`CategoryTheory.Sheaf.H.map` induced by a morphism of sheaves. -/
lemma Etale.cohomologyMap_map {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H F n) :
    Etale.cohomologyMap f G n (Sheaf.H.map φ n x) =
      Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map φ) n (Etale.cohomologyMap f F n x) := by
  simp only [Etale.cohomologyMap_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by lia)).symm

end ComparisonMap

section UniversalHomeomorphism

variable [IsUniversalHomeomorphism f]

attribute [local instance] Scheme.Hom.isEquivalence_etale Etale.isEquivalence_upperStar

/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y` the comparison map `AlgebraicGeometry.Etale.cohomologyMap` on
étale cohomology is bijective in every degree. -/
@[stacks 03SI]
theorem Etale.cohomologyMap_bijective : Function.Bijective (Etale.cohomologyMap f F n) :=
  (Ext.precompAddEquiv _ _ n).bijective.comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects _ _ F n)

/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y` the pullback induces an isomorphism
`H^n(Y_ét, F) ≃+ H^n(X_ét, f^* F)` in every degree. This is
`AlgebraicGeometry.Etale.cohomologyMap`, which is bijective by
`AlgebraicGeometry.Etale.cohomologyMap_bijective`. -/
@[stacks 03SI]
noncomputable def Etale.cohomologyEquiv :
    Sheaf.H F n ≃+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  AddEquiv.ofBijective _ (Etale.cohomologyMap_bijective f F n)

@[simp]
lemma Etale.cohomologyEquiv_apply (x : Sheaf.H F n) :
    Etale.cohomologyEquiv f F n x = Etale.cohomologyMap f F n x :=
  rfl

end UniversalHomeomorphism

end AlgebraicGeometry
