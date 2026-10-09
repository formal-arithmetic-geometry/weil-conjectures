/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Open–closed conservativity and vanishing on the derived category

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j`, for instance `i = j.closedComplement`. This file lifts the two
sheaf-level facts of `WeilConjectures.SixFunctors.OpenClosed.Conservative` and
`WeilConjectures.SixFunctors.OpenClosed.Vanishing` to the unbounded derived categories of étale
sheaves:

- a morphism `φ` of `D(X_ét)` whose restrictions along `j` and `i` are invertible is
  invertible;
- `i^* (j_! K)` vanishes for every `K` in `D(U_ét)`, as soon as the ranges of `j` and `i` are
  disjoint.

Both are first proved for the levelwise functors `D(g^*)`, by the general facts
`CategoryTheory.Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory` and
`CategoryTheory.Functor.isZero_mapDerivedCategory_obj` about exact functors, and then for the
total left derived functors `L(g^*)` through the isomorphism
`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`.

## Main results

- `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_leftDerivedUpperStar`: the pair
  `(Lj^*, Li^*)` jointly reflects isomorphisms, with the two-hypothesis form
  `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map` and the levelwise versions
  `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar` and
  `AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map`
  (blueprint: `prop:openclosed-conservative-derived`).
- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_obj_mapDerivedCategory_\
  openImmersionLowerShriek_of_disjoint_range`: `Li^* (j_! K) = 0`, with the levelwise version
  `AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_\
  openImmersionLowerShriek_of_disjoint_range`
  (blueprint: `lemma:openclosed-vanishing-lowerShriek-derived`).
- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_closedComplement_map` and
  `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_closedComplement_obj_\
  openImmersionLowerShriek`: the two results for `i = j.closedComplement`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conservative

variable {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- `hJ` does not appear in the statements below, and neither do `FC` and `CC` it depends on,
-- so it has to be included by hand; it is needed by the sheaf-level
-- `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar`.
include hJ

/-- **Derived open–closed conservativity**, for the levelwise pullbacks: the pair
`(D(j^*), D(i^*))` jointly reflects isomorphisms of `D(X_ét)`.

On homology sheaves this is the sheaf-level statement, since `j^*` and `i^*` are exact:
```
D(X_ét) --D(g^*)--> D(Y_ét)
   |                   |
  H^n                 H^n
   v                   v
Sh(X_ét) ---g^*---> Sh(Y_ét)
```
commutes up to isomorphism for `g = j, i`.
(blueprint: `prop:openclosed-conservative-derived`) -/
theorem jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor D((j)^*[A]) D((i)^*[A])) :=
  Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (jointlyReflectIsomorphisms_upperStar A j i hij)

/-- **Derived open–closed conservativity**, for the levelwise pullbacks: a morphism `φ` of
`D(X_ét)` such that `D(j^*) φ` and `D(i^*) φ` are invertible is invertible.
(blueprint: `prop:openclosed-conservative-derived`) -/
theorem isIso_of_isIso_mapDerivedCategoryUpperStar_map
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (hj : IsIso (D((j)^*[A]).map φ)) (hi : IsIso (D((i)^*[A]).map φ)) : IsIso φ :=
  (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar A j i hij).isIso_of_pairFunctor φ hj hi

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Derived open–closed conservativity**: the pair `(Lj^*, Li^*)` of total left derived
pullbacks jointly reflects isomorphisms of `D(X_ét)`.
(blueprint: `prop:openclosed-conservative-derived`) -/
theorem jointlyReflectIsomorphisms_leftDerivedUpperStar
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor L((j)^*[A]) L((i)^*[A])) :=
  (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar A j i hij).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory A i).symm

/-- **Derived open–closed conservativity**: a morphism `φ` of `D(X_ét)` such that the derived
restrictions `Lj^* φ` and `Li^* φ` are invertible is invertible.
(blueprint: `prop:openclosed-conservative-derived`) -/
theorem isIso_of_isIso_leftDerivedUpperStar_map
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (hj : IsIso (L((j)^*[A]).map φ)) (hi : IsIso (L((i)^*[A]).map φ)) : IsIso φ :=
  (jointlyReflectIsomorphisms_leftDerivedUpperStar A j i hij).isIso_of_pairFunctor φ hj hi

/-- Derived open–closed conservativity for the closed complement `j.closedComplement` of `j`:
a morphism `φ` of `D(X_ét)` such that `Lj^* φ` and the derived restriction of `φ` to the
closed complement are invertible is invertible. -/
theorem isIso_of_isIso_leftDerivedUpperStar_closedComplement_map
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (hj : IsIso (L((j)^*[A]).map φ)) (hi : IsIso (L((j.closedComplement)^*[A]).map φ)) :
    IsIso φ :=
  isIso_of_isIso_leftDerivedUpperStar_map A j j.closedComplement j.range_closedComplement φ hj hi

end Conservative

section Vanishing

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

/-- **`i^* (j_! K)` vanishes** in `D(Z_ét)`, for the levelwise pullback `D(i^*)`, when the
ranges of `i` and `j` are disjoint. -/
lemma isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero (D((i)^*[A]).obj (D((j)_!open[A]).obj K)) :=
  -- Since `j_!` is exact, `H^n (j_! K) ≅ j_! (H^n K)`, which `i^*` kills.
  Functor.isZero_mapDerivedCategory_obj _ _ fun n ↦
    (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i hij.symm
      ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso
      ((i)^*[A].mapIso (((j)_!open[A].mapDerivedCategoryHomologyFunctorIso n).symm.app K))

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **`Li^* (j_! K)` vanishes** in `D(Z_ét)` when the ranges of `i` and `j` are disjoint.

The homology sheaves of `Li^* (j_! K)` are the `i^* (j_! (H^n K))`, since
```
D(U_ét) --D(j_!)--> D(X_ét) --Li^*--> D(Z_ét)
   |                   |                  |
  H^n                 H^n                H^n
   v                   v                  v
Sh(U_ét) ---j_!---> Sh(X_ét) ---i^*---> Sh(Z_ét)
```
commutes up to isomorphism, and `i^* j_! = 0` on sheaves.
(blueprint: `lemma:openclosed-vanishing-lowerShriek-derived`) -/
lemma isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero (L((i)^*[A]).obj (D((j)_!open[A]).obj K)) :=
  (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
    A j i hij K).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A i).app _)

/-- `Li^* (j_! K)` vanishes on the closed complement `j.closedComplement` of `j`. -/
lemma isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero (L((j.closedComplement)^*[A]).obj (D((j)_!open[A]).obj K)) :=
  isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
    A j j.closedComplement (by rw [j.range_closedComplement]; exact disjoint_compl_left) K

end Vanishing

end AlgebraicGeometry.Etale
