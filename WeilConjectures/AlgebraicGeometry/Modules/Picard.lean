/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Skeleton

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
- `SheafOfModules.Invertible.tensorInv`: a tensor inverse of an invertible sheaf of modules,
  together with `SheafOfModules.Invertible.tensorInvIso`, an isomorphism
  `M ⊗ hM.tensorInv ≅ 𝟙_`.
- `SheafOfModules.Invertible.zpow`: the `m`-th tensor power of an invertible sheaf of modules,
  for an integer exponent `m`, together with the comparison isomorphisms
  `SheafOfModules.Invertible.zpowAddIso`, `zpowNegIso`, `zpowTensorObjIso` and `zpowIso`.
- `SheafOfModules.Pic`: the Picard group of a sheaf of commutative rings on a site.
- `AlgebraicGeometry.Scheme.Pic`: the Picard group of a scheme `X`, i.e. the group of isomorphism
  classes of invertible `𝒪ₓ`-modules under the tensor product.

## Main results

- `SheafOfModules.invertible_iff_exists`: `M` is invertible if and only if there exists `N` such
  that `M ⊗ N` is isomorphic to the tensor unit.
- `SheafOfModules.invertible_iff_isUnit`: unfolding lemma for `SheafOfModules.Invertible`.
- `SheafOfModules.Invertible.tensorObj` and `SheafOfModules.Invertible.tensorPow`: a tensor
  product and a tensor power of invertible sheaves of modules are invertible.
- `SheafOfModules.invertible_cons` and `SheafOfModules.invertible_update`: prepending an
  invertible sheaf of modules to, and replacing one member of, a family of invertible sheaves of
  modules.
- `SheafOfModules.Invertible.isEquivalence_tensorRight`: **tensoring by an invertible sheaf of
  modules is an equivalence of categories**, hence exact; and
  `SheafOfModules.Invertible.isZero_tensorObj`, that it carries zero sheaves to zero sheaves.
- `SheafOfModules.invertible_zpow`: an integer tensor power of an invertible sheaf of modules is
  invertible, with `SheafOfModules.Pic.mk_zpow` recording the corresponding equality in the
  Picard group.
- `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`: two invertible `𝒪ₓ`-modules have the same class
  in the Picard group of `X` if and only if they are isomorphic.
- `AlgebraicGeometry.Scheme.Pic.exists_mk`: every class in the Picard group of `X` is the class
  of an invertible `𝒪ₓ`-module.
- `AlgebraicGeometry.Scheme.Pic.mk_eq_one_iff`: an invertible `𝒪ₓ`-module has trivial class in
  the Picard group of `X` if and only if it is isomorphic to the structure sheaf.

## TODO

- Provide the instance `MonoidalPreadditive (SheafOfModules R')`, equivalently the additivity of
  `CategoryTheory.MonoidalCategory.tensorRight`. The exactness of tensoring recorded here is
  deduced from invertibility, through `SheafOfModules.Invertible.isEquivalence_tensorRight`;
  additivity would give it for an arbitrary `N`, as
  `CategoryTheory.Sheaf.monoidalPreadditive` does for sheaves with values in a monoidal abelian
  category.
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

/-- Prepending an invertible sheaf of modules to a family of invertible sheaves of modules gives
a family of invertible sheaves of modules. -/
theorem invertible_cons {r : ℕ} (hM : M.Invertible)
    {L : Fin r → SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (hL : ∀ i, (L i).Invertible) (i : Fin (r + 1)) :
    ((Fin.cons M L : Fin (r + 1) → _) i).Invertible := by
  induction i using Fin.cases with
  | zero => rwa [Fin.cons_zero]
  | succ i =>
    rw [Fin.cons_succ]
    exact hL i

/-- Replacing one member of a family of invertible sheaves of modules by an invertible sheaf of
modules gives a family of invertible sheaves of modules. -/
theorem invertible_update {ι : Type*} [DecidableEq ι]
    {L : ι → SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (hL : ∀ i, (L i).Invertible) {j : ι} (hM : M.Invertible) (i : ι) :
    (Function.update L j M i).Invertible :=
  (Function.forall_update_iff L fun _ N ↦ N.Invertible).2 ⟨hM, fun i _ ↦ hL i⟩ i

section ZPow

/-- A tensor inverse of an invertible sheaf of modules: the sheaf of modules attached to the
inverse of the class of `M` in the skeleton. -/
noncomputable def Invertible.tensorInv (hM : M.Invertible) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  IsUnit.tensorInv hM

/-- A tensor inverse of an invertible sheaf of modules is invertible. -/
theorem invertible_tensorInv (hM : M.Invertible) : hM.tensorInv.Invertible :=
  isUnit_toSkeleton_tensorInv hM

/-- **`hM.tensorInv` is a tensor inverse of `M`.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def Invertible.tensorInvIso (hM : M.Invertible) : M ⊗ hM.tensorInv ≅ 𝟙_ _ :=
  IsUnit.tensorInvIso hM

/-- **Tensoring by an invertible sheaf of modules is an equivalence of categories**, the inverse
being tensoring by a tensor inverse. In particular it is exact, so it carries a short exact
sequence of sheaves of modules to a short exact sequence by
`CategoryTheory.ShortComplex.ShortExact.map_of_exact`. -/
lemma Invertible.isEquivalence_tensorRight (hM : M.Invertible) :
    (MonoidalCategory.tensorRight M).IsEquivalence :=
  MonoidalCategory.isEquivalence_tensorRight hM.tensorInvIso (β_ _ _ ≪≫ hM.tensorInvIso)

/-- **Tensoring a zero sheaf of modules by an invertible one gives a zero sheaf.** -/
lemma Invertible.isZero_tensorObj (hM : M.Invertible)
    {A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (hA : Limits.IsZero A) : Limits.IsZero (A ⊗ M) :=
  MonoidalCategory.isZero_tensorObj_of_isZero hM.tensorInvIso (β_ _ _ ≪≫ hM.tensorInvIso) hA

/-- The `m`-th tensor power of an invertible sheaf of modules `M`, for an integer exponent `m`:
the `m`-th tensor power of `M` itself when `m ≥ 0`, and the `(-m)`-th tensor power of the tensor
inverse `SheafOfModules.Invertible.tensorInv` when `m < 0`. -/
noncomputable def Invertible.zpow (hM : M.Invertible) (m : ℤ) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  IsUnit.tensorZPow hM m

/-- Integer tensor powers agree with `CategoryTheory.MonoidalCategory.tensorPow` on natural
exponents. -/
@[simp]
lemma Invertible.zpow_natCast (hM : M.Invertible) (n : ℕ) : hM.zpow n = M ^⊗ n := rfl

/-- The zeroth integer tensor power is the tensor unit. -/
@[simp]
lemma Invertible.zpow_zero (hM : M.Invertible) : hM.zpow 0 = 𝟙_ _ := rfl

/-- The first integer tensor power is the first tensor power. -/
lemma Invertible.zpow_one (hM : M.Invertible) : hM.zpow 1 = M ^⊗ 1 := rfl

/-- A negative integer tensor power is a tensor power of the tensor inverse. -/
lemma Invertible.zpow_negSucc (hM : M.Invertible) (n : ℕ) :
    hM.zpow (Int.negSucc n) = hM.tensorInv ^⊗ (n + 1) :=
  rfl

/-- **The class of `hM.zpow m` in the skeleton is the `m`-th power of the class of `M`.** Every
comparison isomorphism between integer tensor powers is read off from this computation. -/
theorem Invertible.toSkeleton_zpow (hM : M.Invertible) (m : ℤ) :
    toSkeleton (hM.zpow m) = ↑(hM.unit ^ m) :=
  toSkeleton_tensorZPow hM m

/-- **An integer tensor power of an invertible sheaf of modules is invertible.** -/
theorem invertible_zpow (hM : M.Invertible) (m : ℤ) : (hM.zpow m).Invertible :=
  isUnit_toSkeleton_tensorZPow hM m

/-- **Integer tensor powers turn addition of exponents into the tensor product.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`; in
particular it does not agree with `CategoryTheory.MonoidalCategory.tensorPowAddIso` when `m` and
`m'` are non-negative. -/
noncomputable def Invertible.zpowAddIso (hM : M.Invertible) (m m' : ℤ) :
    hM.zpow (m + m') ≅ hM.zpow m ⊗ hM.zpow m' :=
  IsUnit.tensorZPowAddIso hM m m'

/-- **A negative integer tensor power of `M` is the corresponding power of a tensor inverse
of `M`.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def Invertible.zpowNegIso (hM : M.Invertible) (m : ℤ) :
    hM.zpow (-m) ≅ (invertible_tensorInv hM).zpow m :=
  IsUnit.tensorZPowNegIso hM m

/-- **Isomorphic invertible sheaves of modules have isomorphic integer tensor powers.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def Invertible.zpowIso (hM : M.Invertible) (hN : N.Invertible) (e : M ≅ N)
    (m : ℤ) : hM.zpow m ≅ hN.zpow m :=
  IsUnit.tensorZPowIso hM hN e m

/-- **An integer tensor power of a tensor product is the tensor product of the integer tensor
powers.**

This is an arbitrary choice of isomorphism, see `CategoryTheory.isoOfToSkeletonEq`. -/
noncomputable def Invertible.zpowTensorObjIso (hM : M.Invertible) (hN : N.Invertible) (m : ℤ) :
    (hM.tensorObj hN).zpow m ≅ hM.zpow m ⊗ hN.zpow m :=
  IsUnit.tensorZPowTensorObjIso hM hN m

end ZPow

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
@[simp]
theorem Pic.mk_tensorObj {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk (M ⊗ N) (hM.tensorObj hN) = Pic.mk M hM * Pic.mk N hN := by
  change (hM.tensorObj hN).unit = hM.unit * hN.unit
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.toSkeleton_tensorObj]

/-- The class of an integer tensor power is the corresponding power of the class. -/
@[simp]
theorem Pic.mk_zpow {hM : M.Invertible} (m : ℤ) :
    Pic.mk (hM.zpow m) (invertible_zpow hM m) = Pic.mk M hM ^ m := by
  change (invertible_zpow hM m).unit = hM.unit ^ m
  exact IsUnit.unit_tensorZPow hM m

variable (R) in
/-- The class of the tensor unit is the unit of the Picard group. -/
@[simp]
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

/-- **Every class in the Picard group of `X` is the class of an invertible `𝒪ₓ`-module**: a
representative is the chosen representative of the isomorphism class in the skeleton. -/
theorem Pic.exists_mk (x : X.Pic) :
    ∃ (M : X.Modules) (hM : M.Invertible), Pic.mk M hM = x := by
  have hx : IsUnit (toSkeleton ((fromSkeleton X.Modules).obj (x : (Skeleton X.Modules)ˣ).val)) := by
    rw [toSkeleton_fromSkeleton_obj]
    exact (x : (Skeleton X.Modules)ˣ).isUnit
  exact ⟨_, hx, Units.ext (α := Skeleton X.Modules)
    (hx.unit_spec.trans (toSkeleton_fromSkeleton_obj _))⟩

/-- Equal invertible `𝒪ₓ`-modules have equal classes in the Picard group of `X`, whichever
proofs of invertibility they are given. -/
theorem Pic.mk_congr {M N : X.Modules} {hM : M.Invertible} {hN : N.Invertible} (h : M = N) :
    Pic.mk M hM = Pic.mk N hN := by
  subst h
  rfl

/-- The class of a tensor product of invertible `𝒪ₓ`-modules is the product of the classes. -/
@[simp]
theorem Pic.mk_tensorObj {M N : X.Modules} {hM : M.Invertible} {hN : N.Invertible} :
    Pic.mk (M ⊗ N) (hM.tensorObj hN) = Pic.mk M hM * Pic.mk N hN := by
  change (hM.tensorObj hN).unit = hM.unit * hN.unit
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.toSkeleton_tensorObj]

/-- The class of an integer tensor power of an invertible `𝒪ₓ`-module is the corresponding power
of the class. -/
@[simp]
theorem Pic.mk_zpow {M : X.Modules} {hM : M.Invertible} (m : ℤ) :
    Pic.mk (hM.zpow m) (SheafOfModules.invertible_zpow hM m) = Pic.mk M hM ^ m := by
  change (SheafOfModules.invertible_zpow hM m).unit = hM.unit ^ m
  exact IsUnit.unit_tensorZPow hM m

/-- The class of a tensor power of an invertible `𝒪ₓ`-module is the corresponding power of the
class. -/
@[simp]
theorem Pic.mk_tensorPow {M : X.Modules} {hM : M.Invertible} (n : ℕ) :
    Pic.mk (M ^⊗ n) (hM.tensorPow n) = Pic.mk M hM ^ (n : ℤ) :=
  Pic.mk_zpow (hM := hM) (n : ℤ)

variable (X) in
/-- The class of the structure sheaf is the unit of the Picard group of `X`. -/
@[simp]
theorem Pic.mk_tensorUnit :
    Pic.mk (𝟙_ X.Modules) (SheafOfModules.invertible_tensorUnit X.sheaf) = 1 := by
  change (SheafOfModules.invertible_tensorUnit X.sheaf).unit = 1
  rw [← Units.val_inj, IsUnit.unit_spec, Units.val_one, Skeleton.one_eq]

/-- An invertible `𝒪ₓ`-module has trivial class in the Picard group of `X` if and only if it is
isomorphic to the structure sheaf. -/
theorem Pic.mk_eq_one_iff {M : X.Modules} {hM : M.Invertible} :
    Pic.mk M hM = 1 ↔ Nonempty (M ≅ 𝟙_ X.Modules) := by
  rw [← Pic.mk_tensorUnit X, Pic.mk_eq_mk_iff]

end AlgebraicGeometry.Scheme
