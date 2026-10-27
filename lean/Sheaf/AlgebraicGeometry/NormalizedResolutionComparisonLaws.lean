/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.AlgebraicGeometry.SmoothNormalizedResolutionRule

/-! # Laws of cartesian normalized resolution comparisons

Source: ILO VIII 2.2.7--2.2.9 and 2.3.4--2.3.5(i).
(blueprint: lem-trf-normalized-resolution-comparison-laws).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A resolution center is nonunit because its support is nonempty.
Source: ILO VIII 2.3.2.
(blueprint: lem-trf-normalized-resolution-comparison-laws). -/
theorem normalizedResolutionCenter_ne_top {X : Scheme.{u}}
    (A : QENormalizedResolutionTower X) (i : Fin A.length) : A.tower.center i ≠ ⊤ := by
  intro h
  simpa [h] using A.nonempty i

/-- The actual identity comparison, using the same tower and identity indices and maps.
Source: ILO VIII 2.2.7--2.2.9 and 2.3.4.
(blueprint: lem-trf-normalized-resolution-comparison-laws). -/
noncomputable def normalizedResolutionIdentityComparison {X : Scheme.{u}}
    (A : QENormalizedResolutionTower X) : QENormalizedResolutionComparison (𝟙 X) A A where
  pulled := A.tower
  initial := A.initial
  lift := fun i ↦ 𝟙 (A.tower.level i)
  base := by simp
  cartesian := fun i ↦ IsPullback.id_horiz (A.toBase i)
  centers := by intro i; simp
  arrows := by intro i; simp
  unit_isIso := by intro i hi; exact (normalizedResolutionCenter_ne_top A i hi).elim
  contraction := {
    index := OrderHom.id
    surjective := Function.surjective_id
    first := rfl
    last := rfl
    iso := fun i ↦ Iso.refl _
    adjacent := fun i ↦ Or.inr ⟨i, rfl, rfl⟩
    deleted := by
      intro i
      constructor
      · intro hi
        have hv := congrArg Fin.val hi
        change i.val + 1 = i.val at hv
        omega
      · rintro ⟨hi, _⟩
        exact (normalizedResolutionCenter_ne_top A i hi).elim
    deletedMap := by
      intro i hi
      have hv := congrArg Fin.val hi
      change i.val + 1 = i.val at hv
      omega
    keptMap := by
      intro i k h₀ h₁
      have hik : i = k := (Fin.castSucc_injective _) h₀
      subst k
      simp
    keptCenter := by
      intro i k h₀ h₁
      have hik : i = k := (Fin.castSucc_injective _) h₀
      subst k
      simp }
  contraction_base := by simp

/-- The actual map of the identity comparison is the identity.
Source: ILO VIII 2.3.4.
(blueprint: lem-trf-normalized-resolution-comparison-laws). -/
theorem normalizedResolutionIdentityComparison_levelMap {X : Scheme.{u}}
    (A : QENormalizedResolutionTower X) (i : Fin (A.length + 1)) :
    (normalizedResolutionIdentityComparison A).levelMap i = 𝟙 (A.tower.level i) := by
  exact Category.id_comp _

/-- Cartesian comparisons of finite-type rational normalized resolution towers obey the
composition and surjectivity laws on surviving indices and actual level maps.
Source: ILO VIII 2.2.7--2.2.9, 2.3.4--2.3.5(i).
(blueprint: lem-trf-normalized-resolution-comparison-laws).

Proof: identify each pulled level with its fibre product by its cartesian square.
Each stage is then the normalized blowup of the prescribed extended ideal. All
levels remain reduced and finite type over the rationals by induction using the
normalized-blowup calculus, since the coherent centers have nowhere dense support. Its
comparison over the base is unique: two such maps coincide over the complement of
the center, which is dense on every reduced source component, and the target blowup
and its finite normalization are separated over the preceding level. Induction from
level zero therefore gives uniqueness of actual maps and of the ordered contraction
indices. For the identity all extended centers remain nonunit, since every center
has nonempty support; the comparison is the identity at every level. For composition,
pull back the two cartesian diagrams successively. Ideal comap is associative and unit
ideals stay unit. Delete first the indices already unit over the middle base and then
those becoming unit over the final base; this is precisely the single ordered deletion
for the composite. The unique level maps are the composites, giving the stated HEq
including their dependent domains. For a surjective base map each pulled level map is
surjective by base change. A point in a center has a preimage and the local stalk map
sends its proper ideal into the maximal ideal there, so the extended center is nonunit.
Thus no adjacent indices coincide, and monotonicity makes the index injective. This
argument includes length zero and empty base schemes. -/
theorem normalizedResolutionComparison_laws
    (I : Type v) (base : I → RationalResolutionInput.{u})
    (T : ∀ X : I, QENormalizedResolutionTower (base X).scheme)
    (C : ∀ (X Y : I) (h : (base Y).scheme ⟶ (base X).scheme), Smooth h →
      QENormalizedResolutionComparison h (T X) (T Y)) :
    (∀ (X Y Z : I) (h : (base Y).scheme ⟶ (base X).scheme)
      (g : (base Z).scheme ⟶ (base Y).scheme)
      (hr : Smooth h) (gr : Smooth g) (ghr : Smooth (g ≫ h)) i,
      (C X Z (g ≫ h) ghr).contraction.index i =
        (C Y Z g gr).contraction.index ((C X Y h hr).contraction.index i)) ∧
    (∀ (X Y Z : I) (h : (base Y).scheme ⟶ (base X).scheme)
      (g : (base Z).scheme ⟶ (base Y).scheme)
      (hr : Smooth h) (gr : Smooth g) (ghr : Smooth (g ≫ h)) i,
      HEq ((C X Z (g ≫ h) ghr).levelMap i)
        ((C Y Z g gr).levelMap ((C X Y h hr).contraction.index i) ≫
          (C X Y h hr).levelMap i)) ∧
    (∀ (X Y : I) (h : (base Y).scheme ⟶ (base X).scheme) (hr : Smooth h), Surjective h →
      Function.Injective (C X Y h hr).contraction.index) := by sorry

end AlgebraicGeometry
