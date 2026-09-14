/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# Invertible sheaves of modules and the Picard group

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The category of sheaves of modules
over the underlying sheaf of rings of `R` is symmetric monoidal, see the file
`WeilConjectures.AlgebraicGeometry.Modules.Monoidal`. A sheaf of modules `M` is *invertible*,
i.e. is a *line bundle*, when it is invertible for this tensor product: when there exists a sheaf
of modules `N` and an isomorphism `M ⊗ N ≅ 𝒪`.

Following `Module.Invertible` and `CommRing.Pic` for modules over a commutative ring,
invertibility is expressed as the invertibility of the class of `M` in the skeleton
`Skeleton (SheafOfModules R')`, which is a commutative monoid because the tensor product is
braided; the Picard group is then the group of units of that commutative monoid. Contrary to
`CommRing.Pic`, no `Shrink` is applied: the Picard group is not asserted to be small.

## Main definitions

- `SheafOfModules.Invertible`: the predicate that a sheaf of modules is invertible.
- `SheafOfModules.Pic`: the Picard group of a sheaf of commutative rings on a site.
- `AlgebraicGeometry.Scheme.Pic`: the Picard group of a scheme `X`, i.e. the group of isomorphism
  classes of invertible `𝒪ₓ`-modules under the tensor product.

## Main results

- `SheafOfModules.invertible_iff_exists`: `M` is invertible if and only if there exists `N` such
  that `M ⊗ N` is isomorphic to the tensor unit.
- `SheafOfModules.invertible_iff_isUnit`: unfolding lemma for `SheafOfModules.Invertible`.
- `SheafOfModules.Invertible.tensorObj` and `SheafOfModules.Invertible.tensorPow`: a tensor
  product and a tensor power of invertible sheaves of modules are invertible.
- `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`: two invertible `𝒪ₓ`-modules have the same class
  in the Picard group of `X` if and only if they are isomorphic.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- A sheaf of modules `M` over (the underlying sheaf of rings of) a sheaf of commutative rings
`R` is *invertible*, i.e. is a *line bundle*, if its class in the skeleton of the symmetric
monoidal category of sheaves of `R`-modules is a unit. Equivalently, there exists a sheaf of
`R`-modules `N` such that `M ⊗ N` is isomorphic to the tensor unit, see
`SheafOfModules.invertible_iff_exists`.

This is the sheafy analogue of `Module.Invertible`. -/
protected def Invertible
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) : Prop :=
  IsUnit (toSkeleton M)

variable {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}

/-- `SheafOfModules.Invertible` unfolds to the invertibility of the class in the skeleton. -/
theorem invertible_iff_isUnit : M.Invertible ↔ IsUnit (toSkeleton M) := Iff.rfl

/-- A sheaf of modules is invertible if and only if it admits a tensor inverse. -/
theorem invertible_iff_exists : M.Invertible ↔ ∃ N, Nonempty (M ⊗ N ≅ 𝟙_ _) := by
  constructor
  · intro hM
    obtain ⟨y, hy⟩ := hM.exists_right_inv
    refine ⟨(fromSkeleton _).obj y, ?_⟩
    rw [← toSkeleton_eq_toSkeleton_iff, Skeleton.toSkeleton_tensorObj,
      toSkeleton_fromSkeleton_obj, ← Skeleton.one_eq]
    exact hy
  · rintro ⟨N, ⟨e⟩⟩
    refine IsUnit.of_mul_eq_one (toSkeleton N) ?_
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq, toSkeleton_eq_toSkeleton_iff]
    exact ⟨e⟩

/-- Invertibility is invariant under isomorphism. -/
theorem Invertible.of_iso (hM : M.Invertible) (e : M ≅ N) : N.Invertible := by
  rw [invertible_iff_isUnit, ← congr_toSkeleton_of_iso e]
  exact hM

/-- Isomorphic sheaves of modules are invertible together. -/
theorem invertible_congr (e : M ≅ N) : M.Invertible ↔ N.Invertible :=
  ⟨fun hM ↦ hM.of_iso e, fun hN ↦ hN.of_iso e.symm⟩

/-- If `M ⊗ N` is isomorphic to the tensor unit, then `M` is invertible. This is the analogue of
`Module.Invertible.left`. -/
theorem Invertible.left (e : M ⊗ N ≅ 𝟙_ _) : M.Invertible :=
  invertible_iff_exists.2 ⟨N, ⟨e⟩⟩

/-- If `M ⊗ N` is isomorphic to the tensor unit, then `N` is invertible. This is the analogue of
`Module.Invertible.right`. -/
theorem Invertible.right (e : M ⊗ N ≅ 𝟙_ _) : N.Invertible :=
  .left (β_ N M ≪≫ e)

variable (R) in
/-- The tensor unit is invertible. -/
theorem invertible_tensorUnit : SheafOfModules.Invertible
    (𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))) :=
  .left (ρ_ _)

variable (R) in
/-- The sheaf of rings `R`, viewed as a sheaf of modules over itself, is invertible. -/
theorem invertible_unit :
    SheafOfModules.Invertible (unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :=
  (invertible_tensorUnit R).of_iso (tensorUnitIso R)

/-- A tensor product of invertible sheaves of modules is invertible. -/
theorem Invertible.tensorObj (hM : M.Invertible) (hN : N.Invertible) :
    SheafOfModules.Invertible (M ⊗ N) := by
  rw [invertible_iff_isUnit, Skeleton.toSkeleton_tensorObj]
  exact IsUnit.mul hM hN

/-- A tensor power of an invertible sheaf of modules is invertible. -/
theorem Invertible.tensorPow (hM : M.Invertible) : ∀ n : ℕ, SheafOfModules.Invertible (M ^⊗ n)
  | 0 => invertible_tensorUnit R
  | n + 1 => (hM.tensorPow n).tensorObj hM

variable (R) in
/-- The Picard group of a sheaf of commutative rings `R` on a site: the group of isomorphism
classes of invertible sheaves of `R`-modules, under the tensor product.

Contrary to `CommRing.Pic`, this is not shrunk down to a small type. -/
def Pic :=
  (Skeleton (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)))ˣ

noncomputable instance : CommGroup (Pic R) :=
  inferInstanceAs (CommGroup
    (Skeleton (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)))ˣ)

/-- The class of an invertible sheaf of modules in the Picard group. -/
protected noncomputable def Pic.mk (M : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (hM : M.Invertible) : Pic R :=
  hM.unit

/-- Two invertible sheaves of modules have the same class in the Picard group if and only if they
are isomorphic. -/
theorem Pic.mk_eq_mk_iff {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk M hM = Pic.mk N hN ↔ Nonempty (M ≅ N) := by
  change hM.unit = hN.unit ↔ _
  rw [← Units.val_inj, hM.unit_spec, hN.unit_spec, toSkeleton_eq_toSkeleton_iff]

/-- The class of a tensor product is the product of the classes. -/
theorem Pic.mk_tensorObj {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk (M ⊗ N) (hM.tensorObj hN) = Pic.mk M hM * Pic.mk N hN := by
  change (hM.tensorObj hN).unit = hM.unit * hN.unit
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.toSkeleton_tensorObj]

variable (R) in
/-- The class of the tensor unit is the unit of the Picard group. -/
theorem Pic.mk_tensorUnit : Pic.mk _ (invertible_tensorUnit R) = 1 := by
  change (invertible_tensorUnit R).unit = 1
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_one, Skeleton.one_eq]

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The Picard group of a scheme `X`: the group of isomorphism classes of invertible
`𝒪ₓ`-modules, under the tensor product.

This is `SheafOfModules.Pic X.sheaf`, spelled directly in terms of the category `X.Modules` of
`𝒪ₓ`-modules. -/
def Pic := (Skeleton X.Modules)ˣ

noncomputable instance : CommGroup X.Pic := inferInstanceAs (CommGroup (Skeleton X.Modules)ˣ)

variable {X}

/-- The class of an invertible `𝒪ₓ`-module in the Picard group of `X`. -/
protected noncomputable def Pic.mk (M : X.Modules) (hM : M.Invertible) : X.Pic :=
  hM.unit

/-- Two invertible `𝒪ₓ`-modules have the same class in the Picard group of `X` if and only if
they are isomorphic. -/
theorem Pic.mk_eq_mk_iff {M N : X.Modules} {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk M hM = Pic.mk N hN ↔ Nonempty (M ≅ N) := by
  change hM.unit = hN.unit ↔ _
  rw [← Units.val_inj, hM.unit_spec, hN.unit_spec, toSkeleton_eq_toSkeleton_iff]

/-- The class of a tensor product of invertible `𝒪ₓ`-modules is the product of the classes. -/
theorem Pic.mk_tensorObj {M N : X.Modules} {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk (M ⊗ N) (hM.tensorObj hN) = Pic.mk M hM * Pic.mk N hN := by
  change (hM.tensorObj hN).unit = hM.unit * hN.unit
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.toSkeleton_tensorObj]

end AlgebraicGeometry.Scheme
