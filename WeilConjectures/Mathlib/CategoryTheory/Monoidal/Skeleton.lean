/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category
public import WeilConjectures.Mathlib.CategoryTheory.Skeletal

/-!
# The skeleton of a monoidal category as a monoid

The skeleton of a monoidal category `C` is a monoid, and this file collects the facts about that
monoid which are used to compute with tensor powers.

The class of a tensor power `X ^⊗ n` in the skeleton is the `n`-th power of the class of `X`.
When the class of `X` is a *unit* of the skeleton, `X` has a tensor inverse
`IsUnit.tensorInv` and an `m`-th tensor power `IsUnit.tensorZPow` for every *integer* `m`,
obtained by inverting the class of `X` in the skeleton and reading the answer back off; the class
of `hX.tensorZPow m` in the skeleton is the `m`-th power of the class of `X`, and every
comparison isomorphism between integer tensor powers is read off from that computation.

Beware that the comparison isomorphisms below are produced by `CategoryTheory.isoOfToSkeletonEq`,
hence are *arbitrary*: unlike `CategoryTheory.MonoidalCategory.tensorPowAddIso`, which is built
from the associator and the right unitor, `IsUnit.tensorZPowAddIso` is not natural in `X`, does
not agree with `tensorPowAddIso` on non-negative exponents, and satisfies no associativity or
unitality coherence. Only the existence of an isomorphism of the stated type is available.

Finally, a monoidal functor `F : C ⥤ D` induces a monoid homomorphism
`CategoryTheory.Skeleton.monoidHom F : Skeleton C →* Skeleton D`. We record that this
construction only depends on `F` up to isomorphism, and that it is compatible with the
identity functor and with the composition of functors.

## Main definitions

- `IsUnit.tensorInv`: a tensor inverse of an object whose class in the skeleton is a unit,
  together with `IsUnit.tensorInvIso`, an isomorphism `X ⊗ hX.tensorInv ≅ 𝟙_ C`.
- `IsUnit.tensorZPow`: the `m`-th tensor power of such an object, for an integer `m`, together
  with the comparison isomorphisms `IsUnit.tensorZPowAddIso`, `IsUnit.tensorZPowNegIso`,
  `IsUnit.tensorZPowTensorObjIso` and `IsUnit.tensorZPowIso`.

## Main results

- `CategoryTheory.Skeleton.toSkeleton_tensorPow`
- `CategoryTheory.toSkeleton_tensorZPow`
- `CategoryTheory.Skeleton.monoidHom_congr`
- `CategoryTheory.Skeleton.monoidHom_id`
- `CategoryTheory.Skeleton.monoidHom_comp`

-/

@[expose] public section

namespace CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

open MonoidalCategory in
@[simp]
lemma Skeleton.toSkeleton_tensorPow (X : C) : ∀ n : ℕ, toSkeleton (X ^⊗ n) = toSkeleton X ^ n
  | 0 => Skeleton.one_eq.symm
  | n + 1 => by
    rw [tensorPow_succ, Skeleton.toSkeleton_tensorObj, Skeleton.toSkeleton_tensorPow X n, pow_succ]

section ZPow

open MonoidalCategory

variable {X Y : C}

/-- A tensor inverse of an object whose class in the skeleton of a monoidal category is a unit:
the object attached to the inverse of that unit. -/
noncomputable def _root_.IsUnit.tensorInv (hX : IsUnit (toSkeleton X)) : C :=
  (fromSkeleton C).obj ↑hX.unit⁻¹

@[simp]
lemma toSkeleton_tensorInv (hX : IsUnit (toSkeleton X)) :
    toSkeleton hX.tensorInv = ↑hX.unit⁻¹ :=
  toSkeleton_fromSkeleton_obj _

/-- The class of a tensor inverse in the skeleton is a unit. -/
lemma isUnit_toSkeleton_tensorInv (hX : IsUnit (toSkeleton X)) :
    IsUnit (toSkeleton hX.tensorInv) := by
  rw [toSkeleton_tensorInv]
  exact Units.isUnit _

@[simp]
lemma _root_.IsUnit.unit_tensorInv (hX : IsUnit (toSkeleton X)) :
    (isUnit_toSkeleton_tensorInv hX).unit = hX.unit⁻¹ := by
  rw [← Units.val_inj, IsUnit.unit_spec, toSkeleton_tensorInv]

/-- **`hX.tensorInv` is a tensor inverse of `X`.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def _root_.IsUnit.tensorInvIso (hX : IsUnit (toSkeleton X)) :
    X ⊗ hX.tensorInv ≅ 𝟙_ C :=
  isoOfToSkeletonEq (by
    have h := Units.mul_inv hX.unit
    rw [hX.unit_spec] at h
    rw [Skeleton.toSkeleton_tensorObj, toSkeleton_tensorInv, h, Skeleton.one_eq])

/-- The `m`-th tensor power of an object `X` of a monoidal category whose class in the skeleton
is a unit, for an integer exponent `m`: the `m`-th tensor power of `X` itself when `m ≥ 0`, and
the `(-m)`-th tensor power of the tensor inverse `IsUnit.tensorInv` otherwise. -/
noncomputable def _root_.IsUnit.tensorZPow (hX : IsUnit (toSkeleton X)) : ℤ → C
  | .ofNat n => X ^⊗ n
  | .negSucc n => hX.tensorInv ^⊗ (n + 1)

/-- Integer tensor powers agree with `CategoryTheory.MonoidalCategory.tensorPow` on natural
exponents. -/
@[simp]
lemma _root_.IsUnit.tensorZPow_natCast (hX : IsUnit (toSkeleton X)) (n : ℕ) :
    hX.tensorZPow n = X ^⊗ n :=
  rfl

/-- The zeroth integer tensor power is the tensor unit. -/
@[simp]
lemma _root_.IsUnit.tensorZPow_zero (hX : IsUnit (toSkeleton X)) : hX.tensorZPow 0 = 𝟙_ C := rfl

/-- The first integer tensor power is the first tensor power. -/
lemma _root_.IsUnit.tensorZPow_one (hX : IsUnit (toSkeleton X)) : hX.tensorZPow 1 = X ^⊗ 1 := rfl

/-- A negative integer tensor power is a tensor power of the tensor inverse. -/
lemma _root_.IsUnit.tensorZPow_negSucc (hX : IsUnit (toSkeleton X)) (n : ℕ) :
    hX.tensorZPow (Int.negSucc n) = hX.tensorInv ^⊗ (n + 1) :=
  rfl

/-- **The class of `hX.tensorZPow m` in the skeleton is the `m`-th power of the class of `X`.**
Every comparison isomorphism between integer tensor powers is read off from this computation. -/
theorem toSkeleton_tensorZPow (hX : IsUnit (toSkeleton X)) (m : ℤ) :
    toSkeleton (hX.tensorZPow m) = ↑(hX.unit ^ m) := by
  obtain n | n := m
  · rw [Int.ofNat_eq_natCast, IsUnit.tensorZPow_natCast, Skeleton.toSkeleton_tensorPow,
      _root_.zpow_natCast, Units.val_pow_eq_pow_val, hX.unit_spec]
  · rw [IsUnit.tensorZPow_negSucc, Skeleton.toSkeleton_tensorPow, toSkeleton_tensorInv,
      zpow_negSucc, ← Units.val_pow_eq_pow_val, inv_pow]

/-- The class of an integer tensor power in the skeleton is a unit. -/
theorem isUnit_toSkeleton_tensorZPow (hX : IsUnit (toSkeleton X)) (m : ℤ) :
    IsUnit (toSkeleton (hX.tensorZPow m)) := by
  rw [toSkeleton_tensorZPow]
  exact Units.isUnit _

@[simp]
lemma _root_.IsUnit.unit_tensorZPow (hX : IsUnit (toSkeleton X)) (m : ℤ) :
    (isUnit_toSkeleton_tensorZPow hX m).unit = hX.unit ^ m := by
  rw [← Units.val_inj, IsUnit.unit_spec, toSkeleton_tensorZPow]

/-- The class of a tensor product in the skeleton is a unit. -/
theorem isUnit_toSkeleton_tensorObj (hX : IsUnit (toSkeleton X)) (hY : IsUnit (toSkeleton Y)) :
    IsUnit (toSkeleton (X ⊗ Y)) := by
  rw [Skeleton.toSkeleton_tensorObj]
  exact hX.mul hY

@[simp]
lemma _root_.IsUnit.unit_tensorObj (hX : IsUnit (toSkeleton X)) (hY : IsUnit (toSkeleton Y)) :
    (isUnit_toSkeleton_tensorObj hX hY).unit = hX.unit * hY.unit := by
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.toSkeleton_tensorObj]

/-- **Integer tensor powers turn addition of exponents into the tensor product.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`; in
particular it does not agree with `CategoryTheory.MonoidalCategory.tensorPowAddIso` when `m` and
`m'` are non-negative. -/
noncomputable def _root_.IsUnit.tensorZPowAddIso (hX : IsUnit (toSkeleton X)) (m m' : ℤ) :
    hX.tensorZPow (m + m') ≅ hX.tensorZPow m ⊗ hX.tensorZPow m' :=
  isoOfToSkeletonEq (by
    rw [toSkeleton_tensorZPow, Skeleton.toSkeleton_tensorObj, toSkeleton_tensorZPow,
      toSkeleton_tensorZPow, ← Units.val_mul, zpow_add])

/-- **A negative integer tensor power of `X` is the corresponding power of a tensor inverse
of `X`.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def _root_.IsUnit.tensorZPowNegIso (hX : IsUnit (toSkeleton X)) (m : ℤ) :
    hX.tensorZPow (-m) ≅ (isUnit_toSkeleton_tensorInv hX).tensorZPow m :=
  isoOfToSkeletonEq (by
    rw [toSkeleton_tensorZPow, toSkeleton_tensorZPow, IsUnit.unit_tensorInv, zpow_neg, inv_zpow])

/-- **Isomorphic objects have isomorphic integer tensor powers.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`; in
particular it does not agree with `CategoryTheory.MonoidalCategory.tensorPowIso` when `m` is
non-negative. -/
noncomputable def _root_.IsUnit.tensorZPowIso (hX : IsUnit (toSkeleton X))
    (hY : IsUnit (toSkeleton Y)) (e : X ≅ Y) (m : ℤ) : hX.tensorZPow m ≅ hY.tensorZPow m :=
  isoOfToSkeletonEq (by
    have h : hX.unit = hY.unit := by
      rw [← Units.val_inj, IsUnit.unit_spec, IsUnit.unit_spec, congr_toSkeleton_of_iso e]
    rw [toSkeleton_tensorZPow, toSkeleton_tensorZPow, h])

/-- **An integer tensor power of a tensor product is the tensor product of the integer tensor
powers**, in a braided monoidal category.

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def _root_.IsUnit.tensorZPowTensorObjIso [BraidedCategory C]
    (hX : IsUnit (toSkeleton X)) (hY : IsUnit (toSkeleton Y)) (m : ℤ) :
    (isUnit_toSkeleton_tensorObj hX hY).tensorZPow m ≅ hX.tensorZPow m ⊗ hY.tensorZPow m :=
  isoOfToSkeletonEq (by
    rw [toSkeleton_tensorZPow, IsUnit.unit_tensorObj, mul_zpow, Units.val_mul,
      Skeleton.toSkeleton_tensorObj, toSkeleton_tensorZPow, toSkeleton_tensorZPow])

end ZPow

@[simp]
lemma Skeleton.monoidHom_toSkeleton (F : C ⥤ D) [F.Monoidal] (X : C) :
    Skeleton.monoidHom F (toSkeleton X) = toSkeleton (F.obj X) :=
  F.mapSkeleton_obj_toSkeleton X

/-- The monoid homomorphism induced on the skeleta by a monoidal functor only depends on the
functor up to isomorphism. -/
lemma Skeleton.monoidHom_congr {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G) :
    Skeleton.monoidHom F = Skeleton.monoidHom G := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton, monoidHom_toSkeleton]
  exact congr_toSkeleton_of_iso (e.app _)

variable (C) in
/-- The identity functor induces the identity of the skeleton. -/
lemma Skeleton.monoidHom_id : Skeleton.monoidHom (𝟭 C) = MonoidHom.id (Skeleton C) := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton]
  rfl

/-- The monoid homomorphism induced on the skeleta by a composition of monoidal functors is
the composition of the induced monoid homomorphisms. -/
lemma Skeleton.monoidHom_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    Skeleton.monoidHom (F ⋙ G) = (Skeleton.monoidHom G).comp (Skeleton.monoidHom F) := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton]
  rw [MonoidHom.comp_apply, monoidHom_toSkeleton, monoidHom_toSkeleton]
  rfl

end CategoryTheory
