/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The power endomorphisms of a group object

Let `G` be a group object in a cartesian monoidal category `C`. Since `X ⟶ G` is a group
for every `X` (`CategoryTheory.Hom.group`), the identity of `G` has powers, and the `n`-th
power of the identity is the endomorphism of `G` that is `x ↦ xⁿ` on points.

## Main definitions

- `CategoryTheory.GrpObj.npow`: the endomorphism `x ↦ xⁿ` of `G`, for `n : ℕ`.
- `CategoryTheory.GrpObj.zpow`: the endomorphism `x ↦ xⁿ` of `G`, for `n : ℤ`.

## Main results

- `CategoryTheory.GrpObj.comp_npow`: composing an `X`-point `f` of `G` with `npow G n` is
  the `n`-th power of `f` in the group `X ⟶ G`. All other properties of `npow` follow from
  this one and the group axioms in `X ⟶ G`.
- `CategoryTheory.GrpObj.instIsMonHomNpow`: `npow G n` is a morphism of monoid objects if
  `G` is commutative.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G H X : C}
  [GrpObj G] [GrpObj H]

open scoped MonObj AddMonObj

namespace GrpObj

variable (G) in
/-- The `n`-th power endomorphism `x ↦ xⁿ` of a group object `G`. -/
@[to_additive /-- The endomorphism `x ↦ n • x` of an additive group object `G`. -/]
def npow (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

variable (G) in
/-- The `n`-th power endomorphism `x ↦ xⁿ` of a group object `G`, for `n : ℤ`. -/
@[to_additive /-- The endomorphism `x ↦ n • x` of an additive group object `G`,
for `n : ℤ`. -/]
def zpow (n : ℤ) : G ⟶ G := (𝟙 G) ^ n

/-- On `X`-points, `npow G n` is the `n`-th power map: this is the defining property of
`npow G n`. -/
@[to_additive (attr := reassoc) /-- On `X`-points, `nsmul G n` is multiplication by `n`: this
is the defining property of `nsmul G n`. -/]
lemma comp_npow (f : X ⟶ G) (n : ℕ) : f ≫ npow G n = f ^ n := by
  rw [npow, MonObj.comp_pow, Category.comp_id]

/-- On `X`-points, `zpow G n` is the `n`-th power map. The name is primed to avoid a clash
with `CategoryTheory.GrpObj.comp_zpow`, which is about powers of a point rather than about
the endomorphism `zpow G n`. -/
@[to_additive (attr := reassoc) /-- On `X`-points, `zsmul G n` is multiplication by `n`. The name
is primed to avoid a clash with `CategoryTheory.AddGrpObj.comp_zsmul`, which is about multiples
of a point rather than about the endomorphism `zsmul G n`. -/]
lemma comp_zpow' (f : X ⟶ G) (n : ℤ) : f ≫ zpow G n = f ^ n := by
  rw [zpow, GrpObj.comp_zpow, Category.comp_id]

variable (G)

@[to_additive (attr := simp)]
lemma npow_zero : npow G 0 = toUnit G ≫ η := by
  rw [npow, pow_zero, Hom.one_def]

@[to_additive (attr := simp) nsmul_one]
lemma npow_one : npow G 1 = 𝟙 G :=
  pow_one _

@[to_additive]
lemma npow_add (m n : ℕ) : npow G (m + n) = lift (npow G m) (npow G n) ≫ μ := by
  rw [← Hom.mul_def, npow, npow, npow, pow_add]

@[to_additive (attr := reassoc)]
lemma npow_comp_npow (m n : ℕ) : npow G m ≫ npow G n = npow G (m * n) := by
  rw [comp_npow, npow, npow, pow_mul]

@[to_additive (attr := simp)]
lemma zpow_natCast (n : ℕ) : zpow G (n : ℤ) = npow G n :=
  _root_.zpow_natCast (𝟙 G) n

@[to_additive (attr := simp) zsmul_neg_one]
lemma zpow_neg_one : zpow G (-1) = ι :=
  (_root_.zpow_neg_one (𝟙 G)).trans inv_eq_inv.symm

variable {G}

/-- The power endomorphisms are natural in the group object. -/
@[to_additive (attr := reassoc) /-- The multiplication by `n` endomorphisms are natural in the
additive group object. -/]
lemma npow_comp (n : ℕ) (f : G ⟶ H) [IsMonHom f] : npow G n ≫ f = f ≫ npow H n := by
  rw [npow, MonObj.pow_comp, Category.id_comp, comp_npow]

/-- The power endomorphisms are natural in the group object. The name is primed to avoid a
clash with `CategoryTheory.GrpObj.zpow_comp`. -/
@[to_additive (attr := reassoc) /-- The multiplication by `n` endomorphisms are natural in the
additive group object. The name is primed to avoid a clash with
`CategoryTheory.AddGrpObj.zsmul_comp`. -/]
lemma zpow_comp' (n : ℤ) (f : G ⟶ H) [IsMonHom f] : zpow G n ≫ f = f ≫ zpow H n := by
  rw [zpow, GrpObj.zpow_comp, Category.id_comp, comp_zpow']

variable [BraidedCategory C] [IsCommMonObj G]

/-- If `G` is a commutative group object, the `n`-th power endomorphism of `G` is a morphism
of monoid objects. -/
@[to_additive /-- If `G` is a commutative additive group object, multiplication by `n` on `G`
is a morphism of additive monoid objects. -/]
instance (n : ℕ) : IsMonHom (npow G n) where
  one_hom := by rw [comp_npow, MonObj.one_eq_one, one_pow]
  mul_hom := by
    have : (npow G n ⊗ₘ npow G n) ≫ μ = (fst G G ≫ npow G n) * (snd G G ≫ npow G n) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [this]
    simp only [comp_npow]
    rw [← mul_pow, ← MonObj.mul_eq_mul]

/-- If `G` is a commutative group object, the `n`-th power endomorphism of `G` is a morphism
of monoid objects, for `n : ℤ`. -/
@[to_additive /-- If `G` is a commutative additive group object, multiplication by `n : ℤ` on
`G` is a morphism of additive monoid objects. -/]
instance (n : ℤ) : IsMonHom (zpow G n) where
  one_hom := by rw [comp_zpow', MonObj.one_eq_one, one_zpow]
  mul_hom := by
    have : (zpow G n ⊗ₘ zpow G n) ≫ μ = (fst G G ≫ zpow G n) * (snd G G ≫ zpow G n) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [this]
    simp only [comp_zpow']
    rw [← mul_zpow, ← MonObj.mul_eq_mul]

end GrpObj

end CategoryTheory
