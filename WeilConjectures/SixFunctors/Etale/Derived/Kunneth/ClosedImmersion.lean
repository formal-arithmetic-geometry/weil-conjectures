/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Tensor products with complexes supported on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion and let

```
  T' --a'--> Z
  |          |
  s          i
  v          v
  T ---a---> X
```

be a cartesian square. For `M ∈ D(Z_ét)` and `N ∈ D(T_ét)` the complex `La^*(Ri_* M) ⊗ᴸ N` is
supported on `T'`, and

`La^*(Ri_* M) ⊗ᴸ N ≅ Rs_*(La'^* M ⊗ᴸ Ls^* N)`.

This holds for arbitrary coefficients: an object `P` of `D(T_ét)` whose restriction to the open
complement of `T'` vanishes is `Rs_* s^* P`, by open–closed conservativity
(`AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar'`), and
`Ls^*` is monoidal while `i^* Ri_* ≅ 𝟭`. No projection formula or proper base change is
involved.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_mapDerivedCategoryUpperStar`:
  `P ≅ Rs_* s^* P` for `P` vanishing on the open complement of the closed immersion `s`.
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar'`:
  `La^*(Ri_* M) ⊗ᴸ N ≅ Rs_*(La'^* M ⊗ᴸ Ls^* N)` and its mirror image.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Supported

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- An object `P` of `D(T_ét)` whose restriction to the open complement `v` of a closed
immersion `s : T' ⟶ T` vanishes is supported on `T'`: the unit `P ⟶ Rs_* s^* P` is an
isomorphism, by open–closed conservativity, as it becomes one after `v^*` (both sides vanish)
and after `s^*` (where it is a section of the counit `s^* Rs_* ⟶ 𝟭`, an isomorphism since
`Rs_*` is fully faithful). -/
theorem nonempty_iso_rightDerivedLowerStar_mapDerivedCategoryUpperStar {T T' V : Scheme.{u}}
    (s : T' ⟶ T) [IsClosedImmersion s] (v : V ⟶ T) [IsOpenImmersion v]
    (hsv : Set.range s.base = (Set.range v.base)ᶜ)
    {P : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (hP : IsZero (D((v)^*[A]).obj P)) :
    Nonempty (P ≅ (R((s)_*[A])).obj (D((s)^*[A]).obj P)) := by
  let adj := mapDerivedUpperStarLowerStarAdjunction A s
  have hd : Disjoint (Set.range v.base) (Set.range s.base) := by
    rw [hsv]
    exact disjoint_compl_right
  have : IsIso (adj.unit.app P) := by
    refine (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A v s hsv).isIso_of_pairFunctor
      _ ?_ ?_
    · exact ⟨⟨0, hP.eq_of_src _ _,
        (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
          A v s hd _).eq_of_src _ _⟩⟩
    · rw [← IsIso.inv_eq_of_inv_hom_id (adj.left_triangle_components P)]
      infer_instance
  exact ⟨asIso (adj.unit.app P)⟩

end Supported

section Tensor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {T T' Z X : Scheme.{u}}

/-- For a closed immersion `i : Z ⟶ X` and `M ∈ D(Z_ét)`, the derived pullback of `Ri_* M` along
`a : T ⟶ X` vanishes on every open `v : V ⟶ T` whose image under `a` misses `Z`. -/
lemma isZero_leftDerivedUpperStar_comp_rightDerivedLowerStar {V : Scheme.{u}} (a : T ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (v : V ⟶ T)
    (hv : ∀ x, a.base (v.base x) ∉ Set.range i.base)
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero ((L((v)^*[A])).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M))) := by
  let u := i.openComplement.ι
  have hu' : Set.range u.base = (Set.range i.base)ᶜ :=
    eq_compl_comm.mp i.range_eq_compl_range_openComplement_ι
  have hu : Set.range (v ≫ a).base ⊆ Set.range u.base := by
    rintro _ ⟨x, rfl⟩
    rw [hu']
    exact hv x
  have hd : Disjoint (Set.range u.base) (Set.range i.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_right
  have h₀ : IsZero ((L((u)^*[A])).obj ((R((i)_*[A])).obj M)) :=
    (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
      A u i hd M).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A u).app _)
  have h₁ := (L((IsOpenImmersion.lift u (v ≫ a) hu)^*[A])).map_isZero h₀
  exact h₁.of_iso (((leftDerivedUpperStarComp A v a).app _).symm ≪≫
    (leftDerivedUpperStarComp A _ u (v ≫ a) (IsOpenImmersion.lift_fac u (v ≫ a) hu).symm).app _)

/-- For a closed immersion `i : Z ⟶ X` and `M ∈ D(Z_ét)`, `Li^*(Ri_* M) ≅ M`. -/
noncomputable def leftDerivedUpperStarRightDerivedLowerStarIso (i : Z ⟶ X) [IsClosedImmersion i]
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (L((i)^*[A])).obj ((R((i)_*[A])).obj M) ≅ M :=
  (leftDerivedUpperStarIsoMapDerivedCategory A i).app _ ≪≫
    asIso ((mapDerivedUpperStarLowerStarAdjunction A i).counit.app M)

/-- The points of `T` over the closed subscheme `Z` lie in the closed subscheme `T'` of a
cartesian square. -/
lemma mem_range_of_isPullback {a : T ⟶ X} {i : Z ⟶ X} {s : T' ⟶ T} {a' : T' ⟶ Z}
    (h : IsPullback a' s i a) (x : T) (hx : a.base x ∈ Set.range i.base) :
    x ∈ Set.range s.base := by
  have hs : Set.range s.base = Set.range (pullback.fst a i).base := by
    rw [← h.flip.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact h.flip.isoPullback.hom.homeomorph.surjective.range_comp _
  rw [hs, Scheme.Pullback.range_fst]
  exact hx

variable [UpperStarPreservesFlat A]

/-- Let `i : Z ⟶ X` be a closed immersion and let

```
  T' --a'--> Z
  |          |
  s          i
  v          v
  T ---a---> X
```

be a cartesian square. For `M ∈ D(Z_ét)` and `N ∈ D(T_ét)`,

`La^*(Ri_* M) ⊗ᴸ N ≅ Rs_*(La'^* M ⊗ᴸ Ls^* N)`.

The left-hand side vanishes on the open complement of `T'`, so it is `Rs_*` of its restriction
to `T'` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_mapDerivedCategoryUpperStar`),
which is computed by the monoidality of `Ls^*` and `Li^* Ri_* ≅ 𝟭`. -/
theorem nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar (a : T ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (s : T' ⟶ T) (a' : T' ⟶ Z) (h : IsPullback a' s i a)
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    Nonempty (((derivedTensor A T).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M))).obj N ≅
      (R((s)_*[A])).obj (((derivedTensor A T').obj ((L((a')^*[A])).obj M)).obj
        ((L((s)^*[A])).obj N))) := by
  have : IsClosedImmersion s :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance
  let v := s.openComplement.ι
  have hP : IsZero (D((v)^*[A]).obj
      (((derivedTensor A T).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M))).obj N)) := by
    refine (isZero_derivedTensor_obj_obj_of_isZero_left
      (isZero_leftDerivedUpperStar_comp_rightDerivedLowerStar A a i v (fun x hx ↦ ?_) M)
      _).of_iso (((leftDerivedUpperStarIsoMapDerivedCategory A v).app _).symm ≪≫
        leftDerivedUpperStarTensorIso A v _ _)
    have := x.2
    exact this (mem_range_of_isPullback h _ hx)
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_mapDerivedCategoryUpperStar A s v
    s.range_eq_compl_range_openComplement_ι hP
  let e₁ : (L((s)^*[A])).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M)) ≅
      (L((a')^*[A])).obj M :=
    ((leftDerivedUpperStarComp A s a (a' ≫ i) h.w).app _).symm ≪≫
      (leftDerivedUpperStarComp A a' i).app _ ≪≫
      (L((a')^*[A])).mapIso (leftDerivedUpperStarRightDerivedLowerStarIso A i M)
  exact ⟨e ≪≫ (R((s)_*[A])).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory A s).app _).symm ≪≫ (R((s)_*[A])).mapIso
      (leftDerivedUpperStarTensorIso A s _ _ ≪≫ ((derivedTensor A T').mapIso e₁).app _)⟩

/-- The mirror image of
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar`:
for a cartesian square as there,

`N ⊗ᴸ La^*(Ri_* M) ≅ Rs_*(Ls^* N ⊗ᴸ La'^* M)`. -/
theorem nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar' (a : T ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (s : T' ⟶ T) (a' : T' ⟶ Z) (h : IsPullback a' s i a)
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    Nonempty (((derivedTensor A T).obj N).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M)) ≅
      (R((s)_*[A])).obj (((derivedTensor A T').obj ((L((s)^*[A])).obj N)).obj
        ((L((a')^*[A])).obj M))) := by
  have : IsClosedImmersion s :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance
  let v := s.openComplement.ι
  have hP : IsZero (D((v)^*[A]).obj
      (((derivedTensor A T).obj N).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M)))) := by
    refine (isZero_derivedTensor_obj_obj_of_isZero_right _
      (isZero_leftDerivedUpperStar_comp_rightDerivedLowerStar A a i v (fun x hx ↦ ?_) M)
      ).of_iso (((leftDerivedUpperStarIsoMapDerivedCategory A v).app _).symm ≪≫
        leftDerivedUpperStarTensorIso A v _ _)
    have := x.2
    exact this (mem_range_of_isPullback h _ hx)
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_mapDerivedCategoryUpperStar A s v
    s.range_eq_compl_range_openComplement_ι hP
  let e₁ : (L((s)^*[A])).obj ((L((a)^*[A])).obj ((R((i)_*[A])).obj M)) ≅
      (L((a')^*[A])).obj M :=
    ((leftDerivedUpperStarComp A s a (a' ≫ i) h.w).app _).symm ≪≫
      (leftDerivedUpperStarComp A a' i).app _ ≪≫
      (L((a')^*[A])).mapIso (leftDerivedUpperStarRightDerivedLowerStarIso A i M)
  exact ⟨e ≪≫ (R((s)_*[A])).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory A s).app _).symm ≪≫ (R((s)_*[A])).mapIso
      (leftDerivedUpperStarTensorIso A s _ _ ≪≫ ((derivedTensor A T').obj _).mapIso e₁)⟩

end Tensor

end Etale

end AlgebraicGeometry
