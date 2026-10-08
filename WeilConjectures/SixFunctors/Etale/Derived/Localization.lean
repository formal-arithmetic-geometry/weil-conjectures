/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The supported localization triangle

For complementary immersions `i : Z ⟶ X` and `j : U ⟶ X` the two adjunction maps of the
exceptional formalism assemble into the *supported localization triangle*

`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]`,

the derived counterpart of the open–closed short exact sequence
`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`. Its first term is
cohomology-with-supports along `Z`; applied to the closed–open pair `(s, j)` on the affine
line it is what computes the fundamental class of the zero section.

The triangle rests on the *closed-immersion unit*: for a closed immersion `i` the exceptional
adjunction unit `Q ⟶ Ri^! Ri_! Q` is an isomorphism, and `Ri_!` is `Ri_*` because `i` is
proper.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`
- `AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek`:
  `D(j^*) Ri_! = 0` when the images of `i` and `j` are disjoint.
- `AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.\
  isZero_of_isZero_mapDerivedCategoryUpperStar_of_isZero_rightDerivedUpperShriek`:
  `D(j^*)` and `Ri^!` jointly detect zero objects.
- `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`
- `AlgebraicGeometry.Etale.supportedLocalizationBoundary`: the boundary of the triangle.
- `AlgebraicGeometry.Etale.exists_triangleHom_supportedLocalization`
- `AlgebraicGeometry.Etale.triangleHom_supportedLocalization_ext`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {U Z X : Scheme.{u}}

/-- Blueprint `sk-prop-sf-closed-unit`: Closed-immersion unit

For a closed immersion `i : Z ⟶ X` and `Q ∈ D^b_{ctf}(Z, Λ)` the unit

`Q ⟶ Ri^! Ri_! Q`

of the exceptional adjunction `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` is
an isomorphism; since a closed immersion is proper, `Ri_!` is `Ri_*`, so this says that `Ri_*`
is fully faithful on the exceptional side. It is the derived counterpart of the full
faithfulness of `i_*` recorded in `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`. -/
theorem isIso_rightDerivedUpperShriekAdjunction_unit_app (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsIso ((rightDerivedUpperShriekAdjunction A i).unit.app Q) :=
  sorry

section Localization

/- The closed symmetric preadditive monoidal structure on the coefficient category: it is
what `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction`, the source of the second
map of the triangle, is stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
/-- The *supported localization triangle* of `L` with connecting map `w`:

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

where `ε` is the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*`. -/
noncomputable abbrev supportedLocalizationTriangle (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (w : (R((j)_*[A])).obj ((L((j)^*[A])).obj L) ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧) :
    Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L)
    ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The open restriction of a compactly supported direct image vanishes away from the image.**
Let `i : Z ⟶ X` be compactifiable and `j : U ⟶ X` an open immersion with disjoint images. Then
`D(j^*) (Ri_! B) = 0` for every `B ∈ D(Z_ét, A)`.

Write `Ri_! = Rp_* ∘ D(i'_!)` for the chosen compactification `Z ⟶[i'] Z̄ ⟶[p] X`, and let
`j' : V ⟶ Z̄` be the base change of `j` along `p`, with `p' : V ⟶ U`. For every `N`,

```
  Hom(N, D(j^*) Rp_* M) ≅ Hom(D(j_!) N, Rp_* M) ≅ Hom(Lp^* D(j_!) N, M)
    ≅ Hom(D(j'_!) Lp'^* N, M) ≅ Hom(Lp'^* N, D(j'^*) M),
```

using `D(j_!) ⊣ D(j^*)`, `Lp^* ⊣ Rp_*`, the base change isomorphism of the extension by zero
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso` and `D(j'_!) ⊣ D(j'^*)`.
For `M = D(i'_!) B` the last group vanishes, because the ranges of `j'` and `i'` are disjoint
(`AlgebraicGeometry.Etale.\
isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range`). -/
theorem isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek (i : Z ⟶ X)
    [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero (D((j)^*[A]).obj ((R(i)_![A]).obj B)) := by
  set c := HasCompactification.compactification i
  have hsq : IsPullback (pullback.snd c.g j) (pullback.fst c.g j) j c.g :=
    (IsPullback.of_hasPullback c.g j).flip
  have hdisj : Disjoint (Set.range (pullback.fst c.g j).base) (Set.range c.i.base) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨v, rfl⟩ ⟨a, ha⟩
    refine Set.disjoint_left.1 hij ⟨a, rfl⟩ ⟨(pullback.snd c.g j).base v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← ha,
      ← Scheme.Hom.comp_apply, ← c.comm]
  have h₀ := isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
    A c.i (pullback.fst c.g j) hdisj B
  set T := D((j)^*[A]).obj ((R(i)_![A]).obj B)
  rw [IsZero.iff_id_eq_zero]
  let e : (T ⟶ T) ≃ (_ ⟶ D((pullback.fst c.g j)^*[A]).obj (D((c.i)_!open[A]).obj B)) :=
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).homEquiv _ _).symm.trans <|
      ((derivedUpperStarLowerStarAdjunction A c.g).homEquiv _ _).symm.trans <|
        (((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).app T).symm.homCongr
          (Iso.refl _)).trans <|
          (derivedOpenImmersionLowerShriekUpperStarAdjunction A _).homEquiv _ _
  have : Subsingleton (T ⟶ T) := e.subsingleton_congr.2 ⟨h₀.eq_of_tgt⟩
  exact Subsingleton.elim _ _

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**No maps from the closed side to the open side.** Let `i : Z ⟶ X` be compactifiable and
`j : U ⟶ X` an open immersion, with disjoint images. Then `Hom((Ri_! B)[n], Rj_* C) = 0` for all
`B ∈ D(Z_ét, A)`, `C ∈ D(U_ét, A)` and `n`. By `D(j^*) ⊣ Rj_*`,

```
  Hom((Ri_! B)[n], Rj_* C) ≅ Hom(D(j^*) ((Ri_! B)[n]), C) ≅ Hom((D(j^*) Ri_! B)[n], C),
```

and `D(j^*) Ri_! = 0` by base change of `Ri_!` along `j`, since the fibre product of the square

```
  Z ×_X U ---> U
     |         | j
     v         v
     Z ---i--> X
```

is empty (`AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek`).
-/
theorem subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (i : Z ⟶ X)
    [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) (n : ℤ) :
    Subsingleton (((R(i)_![A]).obj B)⟦n⟧ ⟶ (R((j)_*[A])).obj C) := by
  have h := (Functor.map_isZero (shiftFunctor _ n)
    (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek A i j hij B)).of_iso
      ((D((j)^*[A]).commShiftIso n).app _)
  exact ((mapDerivedUpperStarLowerStarAdjunction A j).homEquiv _ _).subsingleton_congr.1
    ⟨h.eq_of_src⟩

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The derived lower shriek of a closed immersion is fully faithful**: its exceptional
adjunction unit is invertible by the closed-immersion unit
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`. -/
noncomputable def fullyFaithfulRightDerivedLowerShriek (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] : (R(i)_![A]).FullyFaithful :=
  have : IsIso (rightDerivedUpperShriekAdjunction A i).unit :=
    have := isIso_rightDerivedUpperShriekAdjunction_unit_app A i
    NatIso.isIso_of_isIso_app _
  (rightDerivedUpperShriekAdjunction A i).fullyFaithfulLOfIsIsoUnit

/-- For an open immersion `j`, the counit `D(j^*) Rj_* ⟶ 𝟭` of `D(j^*) ⊣ Rj_*` is an
isomorphism: `D(j_!) ⊣ D(j^*) ⊣ Rj_*` is an adjoint triple whose first unit is invertible
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`). -/
instance isIso_mapDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (mapDerivedUpperStarLowerStarAdjunction A j).counit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨derivedOpenImmersionLowerShriekUpperStarAdjunction A j,
      mapDerivedUpperStarLowerStarAdjunction A j⟩).1 inferInstance

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**Open–closed detection by the exceptional inverse image**: let `i : Z ⟶ X` be a closed
immersion with complementary open `j : U ⟶ X`. An object `E` of `D(X_ét, A)` with
`D(j^*) E = 0` and `Ri^! E = 0` is zero.

This is `CategoryTheory.Adjunction.isZero_of_isZero_rightAdjoint` for
`D(i^*) ⊣ Ri_! ⊣ Ri^!` (with `Ri_! ≅ Ri_*`): the unit `E ⟶ Ri_! D(i^*) E` is inverted by
`D(j^*)` and by `D(i^*)`, hence invertible by open–closed detection
(`AlgebraicGeometry.Etale.isZero_of_isZero_mapDerivedCategoryUpperStar`), and then
`Hom(E, E) ≅ Hom(D(i^*) E, Ri^! E) = 0`. -/
theorem isZero_of_isZero_mapDerivedCategoryUpperStar_of_isZero_rightDerivedUpperShriek
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hj : IsZero (D((j)^*[A]).obj E)) (hi : IsZero ((R(i)^![A]).obj E)) : IsZero E :=
  have := (fullyFaithfulRightDerivedLowerShriek A i).full
  have := (fullyFaithfulRightDerivedLowerShriek A i).faithful
  let adj := (mapDerivedUpperStarLowerStarAdjunction A i).ofNatIsoRight
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).symm
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  (rightDerivedUpperShriekAdjunction A i).isZero_of_isZero_rightAdjoint adj
    (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek A i j
      (hij ▸ disjoint_compl_left))
    (fun _ hj hi ↦ isZero_of_isZero_mapDerivedCategoryUpperStar A j i hij hj hi) hj hi

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The supported localization triangle.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. For `L ∈ D(X_ét, A)` the *adjunction maps*

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

— `ε` the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*` — extend to a
distinguished triangle `supportedLocalizationTriangle A i j L w`, and the connecting map `w` is
*unique*. Under the closed-immersion unit `Ri_! Ri^! L` is cohomology with supports along `Z`.

Existence is `CategoryTheory.Adjunction.exists_distTriang_counit_unit` for `Ri_! ⊣ Ri^!` and
`D(j^*) ⊣ Rj_*`: complete `ε_L` to a distinguished triangle `Ri_! Ri^! L ⟶ L ⟶ C ⟶`; the unit
factors through `L ⟶ C`, and the cone of the factorisation `C ⟶ Rj_* D(j^*) L` is killed by
`D(j^*)` and by `Ri^!`, hence zero
(`AlgebraicGeometry.Etale.\
isZero_of_isZero_mapDerivedCategoryUpperStar_of_isZero_rightDerivedUpperShriek`).
The inputs are `D(j^*) Ri_! = 0`
(`AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek`), the
closed-immersion unit and the full faithfulness of `Rj_*`. The unit of `D(j^*) ⊣ Rj_*` is then
replaced by that of `Lj^* ⊣ Rj_*`.

Uniqueness is [BBD, 1.1.9] applied to two such triangles and the identity of `L`: as
`Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L) = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`), the morphism of
triangles extending `𝟙 L` (`CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`)
has components `(𝟙, 𝟙, 𝟙)`, so the two connecting maps agree. -/
theorem existsUnique_distTriang_supportedLocalization (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃! w, supportedLocalizationTriangle A i j L w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ : ∃ w, supportedLocalizationTriangle A i j L w ∈ distTriang _ := by
    have : IsIso (rightDerivedUpperShriekAdjunction A i).unit :=
      have := isIso_rightDerivedUpperShriekAdjunction_unit_app A i
      NatIso.isIso_of_isIso_app _
    obtain ⟨w, hw⟩ := (rightDerivedUpperShriekAdjunction A i).exists_distTriang_counit_unit
      (mapDerivedUpperStarLowerStarAdjunction A j)
      (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerShriek A i j
        (hij ▸ disjoint_compl_left))
      (fun _ hj hi ↦
        isZero_of_isZero_mapDerivedCategoryUpperStar_of_isZero_rightDerivedUpperShriek A i j hij
          hj hi) L
    -- Replace the unit of `D(j^*) ⊣ Rj_*` by that of `Lj^* ⊣ Rj_*`.
    let e := Adjunction.leftAdjointUniq (derivedUpperStarLowerStarAdjunction A j)
      (mapDerivedUpperStarLowerStarAdjunction A j)
    refine ⟨(R((j)_*[A])).map (e.hom.app L) ≫ w, isomorphic_distinguished _ hw _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((R((j)_*[A])).mapIso (e.app L))
      (by simp) (by simp [e]) (by simp)
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  have : Subsingleton ((supportedLocalizationTriangle A i j L w').obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle A i j L w).obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A i j
      (hij ▸ disjoint_compl_left) _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw' hw (𝟙 _)
    (by rw [Category.id_comp]; exact comp_distTriang_mor_zero₁₂ _ hw')
  have h₁ : τ.hom₁ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hw
    (by rw [← τ.comm₁, hτ, Category.comp_id, Category.id_comp]; rfl)
  have h₃ : τ.hom₃ = 𝟙 _ := Triangle.cancel_mor₂_of_subsingleton hw'
    (by rw [τ.comm₂, hτ, Category.id_comp, Category.comp_id]; rfl)
  have h := τ.comm₃
  rw [h₁, h₃] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h

/-- The *boundary* `δ : Rj_* Lj^* L ⟶ (Ri_! Ri^! L)[1]` of the supported localization triangle
of `L`: the unique connecting map making `supportedLocalizationTriangle A i j L δ`
distinguished.

It is *defined* as `Classical.choose` of the existence half of
`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`; uniqueness is what
makes the choice canonical. The supported term is
`Ri_!`, which for a closed immersion is `Ri_*`. -/
noncomputable def supportedLocalizationBoundary (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (R((j)_*[A])).obj ((L((j)^*[A])).obj L) ⟶ ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧ :=
  (existsUnique_distTriang_supportedLocalization A i j hij L).exists.choose

/-- The supported localization triangle with its boundary
`AlgebraicGeometry.Etale.supportedLocalizationBoundary` is distinguished. -/
theorem supportedLocalizationTriangle_mem_distTriang (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    supportedLocalizationTriangle A i j L (supportedLocalizationBoundary A i j hij L) ∈
      distTriang _ :=
  (existsUnique_distTriang_supportedLocalization A i j hij L).exists.choose_spec

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**Naturality of the supported localization triangle.** Let `i : Z ⟶ X` be compactifiable and
`j : U ⟶ X` an open immersion, with disjoint images. For `φ : L ⟶ L'` and distinguished
supported localization triangles of `L` and `L'`, the triple `(Ri_! Ri^! φ, φ, Rj_* Lj^* φ)`
is a morphism of triangles:

```
  Ri_! Ri^! L  --ε_L-->  L  --η_L-->  Rj_* Lj^* L  --w-->  (Ri_! Ri^! L)[1]
       |                 |                |                     |
   Ri_!Ri^!φ             φ           Rj_*Lj^*φ           (Ri_!Ri^!φ)[1]
       v                 v                v                     v
  Ri_! Ri^! L' --ε_L'--> L' --η_L'--> Rj_* Lj^* L' --w'-->  (Ri_! Ri^! L')[1]
```

The middle component extends to a morphism of triangles
(`CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`) because
`ε_L ≫ φ ≫ η_L' = Ri_! Ri^! φ ≫ ε_L' ≫ η_L' = 0`; its outer components are the ones above
because `Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L') = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`). -/
theorem exists_triangleHom_supportedLocalization (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : L ⟶ L')
    {w : (R((j)_*[A])).obj ((L((j)^*[A])).obj L) ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧}
    {w' : (R((j)_*[A])).obj ((L((j)^*[A])).obj L') ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L'))⟦(1 : ℤ)⟧}
    (hw : supportedLocalizationTriangle A i j L w ∈ distTriang _)
    (hw' : supportedLocalizationTriangle A i j L' w' ∈ distTriang _) :
    ∃ τ : supportedLocalizationTriangle A i j L w ⟶ supportedLocalizationTriangle A i j L' w',
      τ.hom₁ = (R(i)_![A]).map ((R(i)^![A]).map φ) ∧ τ.hom₂ = φ ∧
        τ.hom₃ = (R((j)_*[A])).map ((L((j)^*[A])).map φ) := by
  have : Subsingleton ((supportedLocalizationTriangle A i j L w).obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle A i j L' w').obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A i j hij _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw hw' φ (by
    rw [← Category.assoc]
    erw [← (rightDerivedUpperShriekAdjunction A i).counit_naturality]
    rw [Category.assoc]
    erw [comp_distTriang_mor_zero₁₂ _ hw']
    rw [comp_zero])
  refine ⟨τ, Triangle.cancel_mor₁_of_subsingleton hw' ?_, hτ,
    Triangle.cancel_mor₂_of_subsingleton hw ?_⟩
  · rw [← τ.comm₁, hτ]
    exact ((rightDerivedUpperShriekAdjunction A i).counit_naturality φ).symm
  · rw [τ.comm₂, hτ]
    exact ((derivedUpperStarLowerStarAdjunction A j).unit_naturality φ).symm

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**A morphism of supported localization triangles is determined by its middle component.** Let
`i : Z ⟶ X` be compactifiable and `j : U ⟶ X` an open immersion, with disjoint images. Two
morphisms between distinguished supported localization triangles with the same middle component
are equal
(`CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`), because
`Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L') = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`) [BBD, 1.1.9]. -/
theorem triangleHom_supportedLocalization_ext (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {w : (R((j)_*[A])).obj ((L((j)^*[A])).obj L) ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧}
    {w' : (R((j)_*[A])).obj ((L((j)^*[A])).obj L') ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L'))⟦(1 : ℤ)⟧}
    (hw : supportedLocalizationTriangle A i j L w ∈ distTriang _)
    (hw' : supportedLocalizationTriangle A i j L' w' ∈ distTriang _)
    {τ τ' : supportedLocalizationTriangle A i j L w ⟶ supportedLocalizationTriangle A i j L' w'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' :=
  have : Subsingleton ((supportedLocalizationTriangle A i j L w).obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle A i j L' w').obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A i j hij _ _ 1
  triangleHom_ext_of_subsingleton hw hw' h

end Localization

end Etale

end AlgebraicGeometry
