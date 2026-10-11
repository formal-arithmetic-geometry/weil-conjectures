/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Supported
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
  (blueprint: `prop:openclosed-conservative-derived`). These need a concrete coefficient
  category; `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar'`
  is the levelwise version for arbitrary coefficients, deduced from
  `WeilConjectures.SixFunctors.OpenClosed.Supported`.
- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_obj_mapDerivedCategory_\
  openImmersionLowerShriek_of_disjoint_range`: `Li^* (j_! K) = 0`, with the levelwise version
  `AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_\
  openImmersionLowerShriek_of_disjoint_range`
  (blueprint: `lemma:openclosed-vanishing-lowerShriek-derived`).
- `AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_\
  of_disjoint_range`: `j^* (Ri_* N) = 0`.
- `AlgebraicGeometry.Etale.exists_distTriang_openClosed`,
  `AlgebraicGeometry.Etale.existsUnique_distTriang_openClosed` and
  `AlgebraicGeometry.Etale.openClosedTriangle_comm₃`: the open–closed triangle, unique and
  functorial
  `j_! j^* M ⟶ M ⟶ Ri_* i^* M ⟶ (j_! j^* M)[1]`
  (blueprint: `sk-prop-sf-open-closed-triangle`).
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

section ConservativeAbstract

variable {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

/-- **Derived open–closed conservativity, for arbitrary coefficients**: the pair
`(D(j^*), D(i^*))` jointly reflects isomorphisms of `D(X_ét, A)` for any Grothendieck abelian
`A`. This is `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar`
without concreteness assumptions on `A`, deduced in the same way from the sheaf-level
`AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar'`.
(blueprint: `prop:openclosed-conservative-derived`) -/
theorem jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar'
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor D((j)^*[A]) D((i)^*[A])) :=
  Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (jointlyReflectIsomorphisms_upperStar' A i hij)

end ConservativeAbstract

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

/-- **`j^* (Ri_* N)` vanishes** in `D(U_ét)` when the ranges of `i` and `j` are disjoint.
Representing `N` by a K-injective complex `I`, `Ri_* N` is `i_* I`, and `j^* i_* I` vanishes
termwise by `AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`. -/
lemma isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
    (hij : Disjoint (Set.range j.base) (Set.range i.base))
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero (D((j)^*[A]).obj (R((i)_*[A]).obj N)) := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have hC : IsZero ((((i)_*[A] ⋙ (j)^*[A]).mapHomologicalComplex _).obj I) := by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    exact (isZero_upperStar_lowerStar_of_disjoint_range A j i hij (I.X n)).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hC).of_iso
    (D((j)^*[A]).mapIso (R((i)_*[A]).mapIso e ≪≫ ((i)_*[A]).rightDerivedFunctorObjQIso I) ≪≫
      ((j)^*[A]).mapDerivedCategoryFactors.app _)

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

section Triangle

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

open Pretriangulated in
/-- Blueprint `sk-prop-sf-open-closed-triangle`: The open–closed triangle

Let `j : U ⟶ X` and `i : Z ⟶ X` be complementary open and closed immersions. For every
`M ∈ D(X_ét, A)` the counit of `D(j_!) ⊣ D(j^*)` and the unit of `D(i^*) ⊣ Ri_*` extend to a
distinguished triangle

```
  j_! j^* M ⟶ M ⟶ Ri_* i^* M ⟶ (j_! j^* M)[1].
```

It is the derived form of the open–closed short exact sequence
`0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`
(`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`).

The proof completes the counit to a distinguished triangle `j_! j^* M ⟶ M ⟶[g] C` and
identifies `C` with `Ri_* i^* M`. Applying `j^*` kills `C`, the counit becoming invertible;
applying `i^*` makes `g` invertible, as `i^* j_! = 0`. Hence the unit `C ⟶ Ri_* i^* C` is
invertible: after `j^*` both ends vanish (`j^* Ri_* = 0`), and after `i^*` it is inverse to the
counit of `D(i^*) ⊣ Ri_*`, an isomorphism because `Ri_*` is fully faithful
(`CategoryTheory.Functor.full_rightDerivedFunctor`); so it is invertible by open–closed
conservativity (`AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar'`),
which holds for arbitrary coefficients. By naturality of the unit, `g` followed by
`C ≅ Ri_* i^* C ≅ Ri_* i^* M` is the unit at `M`. -/
theorem exists_distTriang_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃ w, Pretriangulated.Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) w ∈ distTriang _ := by
  have hd : Disjoint (Set.range i.base) (Set.range j.base) := by
    rw [hij]; exact disjoint_compl_left
  let adj := mapDerivedUpperStarLowerStarAdjunction A i
  let adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  -- complete the counit `j_! j^* M ⟶ M` to a distinguished triangle `j_! j^* M ⟶ M ⟶ C`
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj'.counit.app M)
  -- `j^* C = 0`, since `j^*` of the counit is invertible
  have hCj : IsZero (D((j)^*[A]).obj C) := by
    refine (Triangle.isZero₃_iff_isIso₁ _ (D((j)^*[A]).map_distinguished _ hT)).2 ?_
    change IsIso (D((j)^*[A]).map (adj'.counit.app M))
    rw [← IsIso.inv_eq_of_hom_inv_id (adj'.right_triangle_components M)]
    infer_instance
  -- `i^* g` is invertible, since `i^* j_! j^* M = 0`
  have hgi : IsIso (D((i)^*[A]).map g) :=
    (Triangle.isZero₁_iff_isIso₂ _ (D((i)^*[A]).map_distinguished _ hT)).1
      (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
        A j i hd _)
  -- the unit `C ⟶ Ri_* i^* C` is invertible, by open–closed conservativity
  have hηC : IsIso (adj.unit.app C) := by
    refine (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A j i hij).isIso_of_pairFunctor
      _ ?_ ?_
    · exact ⟨⟨0, hCj.eq_of_src _ _,
        (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
          A j i hd.symm _).eq_of_src _ _⟩⟩
    · rw [← IsIso.inv_eq_of_inv_hom_id (adj.left_triangle_components C)]
      infer_instance
  let e : C ≅ R((i)_*[A]).obj (D((i)^*[A]).obj M) :=
    asIso (adj.unit.app C) ≪≫ R((i)_*[A]).mapIso (asIso (D((i)^*[A]).map g)).symm
  have he : g ≫ e.hom = adj.unit.app M := by
    have := adj.unit.naturality g
    dsimp at this
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% this, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp [adj'])
    (by rw [← he]; simp) (by simp)

omit [IsClosedImmersion i] in
/-- **Hom vanishing** for the open–closed pair: every morphism from a shift of an extension by
zero `j_! N` to a closed direct image `Ri_* M` vanishes, since by `D(j_!) ⊣ D(j^*)` it corresponds
to a morphism into `j^* Ri_* M = 0`. -/
lemma eq_zero_of_shift_openImmersionLowerShriek_to_rightDerivedLowerStar
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (N : DerivedCategory (Sheaf U.smallEtaleTopology A)) (n : ℤ)
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (φ : (D((j)_!open[A]).obj N)⟦n⟧ ⟶ R((i)_*[A]).obj M) : φ = 0 := by
  have hd : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [hij]; exact disjoint_compl_right
  let adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have h₀ : (D((j)_!open[A]).commShiftIso n).hom.app N ≫ φ = 0 := by
    apply adj'.homEquiv _ _ |>.injective
    exact (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
      A j i hd M).eq_of_tgt _ _
  simpa using (D((j)_!open[A]).commShiftIso n).inv.app N ≫= h₀

open Pretriangulated in
/-- Blueprint `lem-cbc-open-closed-recollement`: Open–closed recollement

For complementary open and closed immersions `j : U ⟶ X` and `i : Z ⟶ X` and every
`M ∈ D(X_ét, A)`, the open counit `j_! j^* M ⟶ M` and the closed unit `M ⟶ Ri_* i^* M` extend
to a distinguished triangle, *uniquely*: the connecting morphism
`w : Ri_* i^* M ⟶ (j_! j^* M)[1]` is determined by the first two arrows, because
`Hom((j_! j^* M)[1], Ri_* i^* M) = 0`
(`AlgebraicGeometry.Etale.eq_zero_of_shift_openImmersionLowerShriek_to_rightDerivedLowerStar`).
Functoriality of the triangle is `AlgebraicGeometry.Etale.openClosedTriangle_comm₃`. This is
the open–closed recollement triangle of blueprint `def-weil-open-closed-recollement` on the
étale site. -/
theorem existsUnique_distTriang_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃! w, Pretriangulated.Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A j i hij M
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism _ _ hw hw' (𝟙 _) (𝟙 _)
    (by simp)
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hw (c - 𝟙 _) (by
    rw [Preadditive.comp_sub, hc₁]; simp)
  rw [eq_zero_of_shift_openImmersionLowerShriek_to_rightDerivedLowerStar A j i hij _ 1 _ g,
    Limits.comp_zero, sub_eq_zero] at hg
  rw [hg] at hc₂
  simpa using hc₂.symm

omit [IsClosedImmersion i] in
open Pretriangulated in
/-- Blueprint `lem-cbc-open-closed-recollement`: Open–closed recollement

**Functoriality.** The open–closed triangles are natural in `M`: for `φ : M ⟶ M'` and the
connecting morphisms `w, w'` of the triangles of `M` and `M'`
(`AlgebraicGeometry.Etale.existsUnique_distTriang_openClosed`), the square formed by `w`, `w'`,
`Ri_* i^* φ` and `(j_! j^* φ)[1]` commutes, so that `(j_! j^* φ, φ, Ri_* i^* φ)` is a morphism of
distinguished triangles. -/
theorem openClosedTriangle_comm₃ (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    {w : R((i)_*[A]).obj (D((i)^*[A]).obj M) ⟶
      (D((j)_!open[A]).obj (D((j)^*[A]).obj M))⟦(1 : ℤ)⟧}
    {w' : R((i)_*[A]).obj (D((i)^*[A]).obj M') ⟶
      (D((j)_!open[A]).obj (D((j)^*[A]).obj M'))⟦(1 : ℤ)⟧}
    (hw : Pretriangulated.Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) w ∈ distTriang _)
    (hw' : Pretriangulated.Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M')
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M') w' ∈ distTriang _) :
    w ≫ (D((j)_!open[A]).map (D((j)^*[A]).map φ))⟦(1 : ℤ)⟧' =
      R((i)_*[A]).map (D((i)^*[A]).map φ) ≫ w' := by
  set T := Pretriangulated.Triangle.mk
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)
    ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) w
  set T' := Pretriangulated.Triangle.mk
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M')
    ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M') w'
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T T' hw hw'
    (D((j)_!open[A]).map (D((j)^*[A]).map φ)) φ
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.naturality φ).symm
  have hu := (mapDerivedUpperStarLowerStarAdjunction A i).unit.naturality φ
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hw
    (c - show T.obj₃ ⟶ T'.obj₃ from R((i)_*[A]).map (D((i)^*[A]).map φ)) (by
    rw [Preadditive.comp_sub, hc₁, sub_eq_zero]; exact hu)
  rw [eq_zero_of_shift_openImmersionLowerShriek_to_rightDerivedLowerStar A j i hij _ 1 _ g,
    Limits.comp_zero, sub_eq_zero] at hg
  rw [hg] at hc₂
  simpa [T, T'] using hc₂

end Triangle

end AlgebraicGeometry.Etale
