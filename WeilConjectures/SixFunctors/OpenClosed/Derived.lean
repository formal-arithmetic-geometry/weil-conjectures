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

/-!
# Open–closed conservativity and vanishing on the derived category

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j` (for instance `i = j.closedComplement`,
`AlgebraicGeometry.Scheme.Hom.closedComplement`). This file lifts the two sheaf-level facts of
`WeilConjectures.SixFunctors.OpenClosed.Conservative` and
`WeilConjectures.SixFunctors.OpenClosed.Vanishing` to the unbounded derived categories of étale
sheaves:

- a morphism `φ` of `D(X_ét)` whose derived restrictions `Lj^* φ` and `Li^* φ` are invertible
  is invertible;
- `Li^* (j_! K)` vanishes for every `K` in `D(U_ét)`, as soon as the ranges of `j` and `i` are
  disjoint.

Both are reduced to the sheaf level through the homology sheaves: a morphism of the derived
category is an isomorphism iff it induces isomorphisms on all homology sheaves
(`DerivedCategory.isIso_iff`), and the exact functors `g^*` and `j_!` commute with taking
homology (`Functor.mapDerivedCategoryHomologyFunctorIso`).

## Main results

- `AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map` and
  `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map`: derived open–closed
  conservativity, for the levelwise and for the total left derived pullbacks.
- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_obj_mapDerivedCategory_\
  openImmersionLowerShriek_of_disjoint_range`: `Li^* (j_! K) = 0`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale MonoidalCategory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conservative

variable {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hij hJ in
/-- **Derived open–closed conservativity**, for the levelwise pullbacks: a morphism `φ` of
`D(X_ét)` such that `j^* φ` and `i^* φ` are invertible is invertible. On the `n`-th homology
sheaf, `j^*` and `i^*` send `H^n φ` to `H^n (j^* φ)` and `H^n (i^* φ)`, which are invertible,
so `H^n φ` is invertible by `AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map`. -/
theorem Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (hj : IsIso (D((j)^*[A]).map φ)) (hi : IsIso (D((i)^*[A]).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map A j i hij _ ?_ ?_
  · refine (NatIso.isIso_map_iff ((j)^*[A].mapDerivedCategoryHomologyFunctorIso n) φ).2 ?_
    rw [Functor.comp_map]
    infer_instance
  · refine (NatIso.isIso_map_iff ((i)^*[A].mapDerivedCategoryHomologyFunctorIso n) φ).2 ?_
    rw [Functor.comp_map]
    infer_instance

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

include hij hJ in
/-- **Derived open–closed conservativity**: a morphism `φ` of `D(X_ét)` such that the derived
restrictions `Lj^* φ` and `Li^* φ` are invertible is invertible. The derived pullbacks are the
levelwise ones (`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`), so this
is `AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map`. -/
theorem Etale.isIso_of_isIso_leftDerivedUpperStar_map
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (hj : IsIso (L((j)^*[A]).map φ)) (hi : IsIso (L((i)^*[A]).map φ)) : IsIso φ :=
  Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map A j i hij φ
    ((NatIso.isIso_map_iff (Etale.leftDerivedUpperStarIsoMapDerivedCategory A j) φ).1 hj)
    ((NatIso.isIso_map_iff (Etale.leftDerivedUpperStarIsoMapDerivedCategory A i) φ).1 hi)

end Conservative

section Vanishing

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- An object of the derived category of an abelian category all of whose homology objects
vanish is zero. -/
private lemma isZero_of_forall_isZero_homologyFunctor_obj {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C)
    (hK : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj K)) : IsZero K := by
  have : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.isIso_iff]
    exact fun n ↦ ⟨0, (hK n).eq_of_src _ _, (hK n).eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : K ⟶ K), comp_zero]

/-- **`Li^* (j_! K)` vanishes** when the ranges of `j` and `i` are disjoint. Its `n`-th homology
sheaf is `i^* (j_! (H^n K))`, the exact functors `i^*` and `j_!` commuting with homology, and
that vanishes by
`AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range`. -/
lemma isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero (L((i)^*[A]).obj (D((j)_!open[A]).obj K)) := by
  refine (isZero_of_forall_isZero_homologyFunctor_obj _ fun n ↦ ?_).of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory A i).app _)
  refine (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i hji
    ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso ?_
  exact ((i)^*[A].mapDerivedCategoryHomologyFunctorIso n).symm.app _ ≪≫
    (i)^*[A].mapIso (((j)_!open[A].mapDerivedCategoryHomologyFunctorIso n).symm.app K)

end Etale

end Vanishing

end AlgebraicGeometry
