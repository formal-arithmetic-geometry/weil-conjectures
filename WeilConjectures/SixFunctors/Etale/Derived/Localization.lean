/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
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
- `AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`
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
theorem isIso_rightDerivedUpperShriekAdjunction_unit_app [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (i : Z ⟶ X) [IsClosedImmersion i]
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

**No maps from the closed side to the open side.** Let `i : Z ⟶ X` and `j : U ⟶ X` have
disjoint images, with `i` compactifiable. Then `Hom((Ri_! B)[n], Rj_* C) = 0` for all
`B ∈ D(Z_ét, A)`, `C ∈ D(U_ét, A)` and `n`. By `Lj^* ⊣ Rj_*`,

```
  Hom((Ri_! B)[n], Rj_* C) ≅ Hom(Lj^* ((Ri_! B)[n]), C) ≅ Hom((Lj^* Ri_! B)[n], C),
```

and `Lj^* Ri_! = 0` by base change of `Ri_!` along `j`, since the fibre product of the square

```
  Z ×_X U ---> U
     |         | j
     v         v
     Z ---i--> X
```

is empty. -/
theorem subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (i : Z ⟶ X)
    [HasCompactification i] (j : U ⟶ X) (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) (n : ℤ) :
    Subsingleton (((R(i)_![A]).obj B)⟦n⟧ ⟶ (R((j)_*[A])).obj C) :=
  sorry

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The supported localization triangle.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. For `L ∈ D(X_ét, A)` the *adjunction maps*

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

— `ε` the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*` — extend to a
distinguished triangle `supportedLocalizationTriangle A i j L w`, and the connecting map `w` is
*unique*. Under the closed-immersion unit `Ri_! Ri^! L` is cohomology with supports along `Z`.

The triangle is the derived form of the open–closed sequence, obtained from the open–closed
triangle by the closed-immersion unit and the determination of a natural transformation on a
generating class.

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
  obtain ⟨w, hw⟩ : ∃ w, supportedLocalizationTriangle A i j L w ∈ distTriang _ := sorry
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
`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`, which is not yet
proved; uniqueness, which is proved, is what makes the choice canonical. The supported term is
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

**Naturality of the supported localization triangle.** Let `i : Z ⟶ X` and `j : U ⟶ X` have
disjoint images. For `φ : L ⟶ L'` and distinguished supported localization triangles of `L` and
`L'`, the triple `(Ri_! Ri^! φ, φ, Rj_* Lj^* φ)` is a morphism of triangles:

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
    (j : U ⟶ X) (hij : Disjoint (Set.range i.base) (Set.range j.base))
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
`i : Z ⟶ X` and `j : U ⟶ X` have disjoint images. Two morphisms between distinguished supported
localization triangles with the same middle component are equal
(`CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`), because
`Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L') = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`) [BBD, 1.1.9]. -/
theorem triangleHom_supportedLocalization_ext (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) (hij : Disjoint (Set.range i.base) (Set.range j.base))
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
