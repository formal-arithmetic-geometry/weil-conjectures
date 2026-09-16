/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.Mathlib.CategoryTheory.Skeletal

/-!
# Integer tensor powers of an invertible sheaf of modules

Let `X` be a scheme and `L` an invertible `𝒪ₓ`-module, that is, a sheaf of modules admitting a
tensor inverse in the sense of `SheafOfModules.Invertible`. The tensor power `L ^⊗ n` is defined
for `n : ℕ` by `CategoryTheory.MonoidalCategory.tensorPow`; this file extends it to an integer
exponent.

The construction chooses a tensor inverse `hL.inv` of `L` — the class of `L` in the skeleton of
`X.Modules` is a unit, and `hL.inv` is the object attached to the inverse unit — and sets
`hL.zpow m` to be `L ^⊗ m` for `m ≥ 0` and `hL.inv ^⊗ (-m)` for `m < 0`. All the comparison
isomorphisms are then read off from the single computation
`SheafOfModules.Invertible.toSkeleton_zpow`, which says that the class of `hL.zpow m` in the
skeleton is the `m`-th power of the class of `L`; an equality of classes in the skeleton is
turned back into an isomorphism of sheaves of modules by `CategoryTheory.isoOfToSkeletonEq`.
Note that the results below are stated as *isomorphisms of sheaves of modules*, not as equalities
in the Picard group: what consumes them applies additive invariants such as the Euler
characteristic to the objects themselves.

Tensoring a coherent sheaf of modules by an invertible one preserves coherence: on an open
subset trivialising `L` the tensor product `F ⊗ L` is isomorphic to `F`, and both quasi-coherence
and being of finite type are local on the base. Consequently the sheaf
`F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` attached to a finite family of invertible sheaves and an integer
vector `m : Fin r → ℤ` is coherent; this is the sheaf whose Euler characteristic is the subject
of Snapper's theorem.

## Main definitions

- `SheafOfModules.Invertible.toUnit`: the class of an invertible sheaf of modules as a unit of
  the skeleton of `X.Modules`.
- `SheafOfModules.Invertible.inv`: a tensor inverse of an invertible sheaf of modules.
- `SheafOfModules.Invertible.zpow`: the `m`-th tensor power `hL.zpow m` of an invertible sheaf
  of modules, for `m : ℤ`.
- `AlgebraicGeometry.Scheme.Modules.tensorZPow`: the sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r`
  attached to a coherent sheaf `F`, a finite family of invertible sheaves `L` and an integer
  vector `m`.

## Main results

- `SheafOfModules.Invertible.zpow_natCast`: `hL.zpow n` is `L ^⊗ n` for a natural number `n`.
- `SheafOfModules.Invertible.zpowAddIso`: `hL.zpow (m + m') ≅ hL.zpow m ⊗ hL.zpow m'`.
- `SheafOfModules.Invertible.zpowZeroIso`: `hL.zpow 0 ≅ 𝒪ₓ`.
- `SheafOfModules.Invertible.invertible_zpow`: an integer tensor power of an invertible sheaf of
  modules is invertible.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_tensorObj_of_invertible`: the tensor product of a
  coherent sheaf of modules with an invertible one is coherent.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_tensorZPow`: the sheaf
  `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` is coherent.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace SheafOfModules

open AlgebraicGeometry

variable {X : Scheme.{u}} {L : X.Modules}

/-- The class of an invertible sheaf of modules as a unit of the skeleton of `X.Modules`.

This is `AlgebraicGeometry.Scheme.Pic.mk`, with its type spelled out so that the unit and its
coercion are literally about `Skeleton X.Modules`. -/
noncomputable def Invertible.toUnit (hL : L.Invertible) : (Skeleton X.Modules)ˣ := hL.unit

@[simp]
lemma Invertible.val_toUnit (hL : L.Invertible) : ↑hL.toUnit = toSkeleton L := hL.unit_spec

/-- A tensor inverse of an invertible sheaf of modules on a scheme: the object of `X.Modules`
attached to the inverse of the class of `L` in the skeleton of `X.Modules`. -/
noncomputable def Invertible.inv (hL : L.Invertible) : X.Modules :=
  (fromSkeleton X.Modules).obj ↑hL.toUnit⁻¹

@[simp]
lemma Invertible.toSkeleton_inv (hL : L.Invertible) : toSkeleton hL.inv = ↑hL.toUnit⁻¹ :=
  toSkeleton_fromSkeleton_obj _

/-- A tensor inverse of an invertible sheaf of modules is invertible. -/
theorem Invertible.invertible_inv (hL : L.Invertible) : hL.inv.Invertible := by
  change IsUnit (toSkeleton hL.inv)
  rw [hL.toSkeleton_inv]
  exact Units.isUnit _

/-- The `m`-th tensor power of an invertible sheaf of modules `L` on a scheme, for an integer
exponent `m`: the `m`-th tensor power of `L` itself when `m ≥ 0`, and the `(-m)`-th tensor power
of a tensor inverse of `L` when `m < 0`. -/
noncomputable def Invertible.zpow (hL : L.Invertible) : ℤ → X.Modules
  | .ofNat n => L ^⊗ n
  | .negSucc n => hL.inv ^⊗ (n + 1)

/-- **Integer tensor powers agree with `tensorPow` on natural exponents.** -/
@[simp]
lemma Invertible.zpow_natCast (hL : L.Invertible) (n : ℕ) : hL.zpow n = L ^⊗ n := rfl

lemma Invertible.zpow_ofNat (hL : L.Invertible) (n : ℕ) :
    hL.zpow (Int.ofNat n) = L ^⊗ n := rfl

/-- The zeroth integer tensor power is the tensor unit. -/
@[simp]
lemma Invertible.zpow_zero (hL : L.Invertible) : hL.zpow 0 = 𝟙_ X.Modules := rfl

lemma Invertible.zpow_negSucc (hL : L.Invertible) (n : ℕ) :
    hL.zpow (Int.negSucc n) = hL.inv ^⊗ (n + 1) := rfl

/-- **The class of `hL.zpow m` in the skeleton of `X.Modules` is the `m`-th power of the class
of `L`.** Every comparison isomorphism below is read off from this computation. -/
theorem Invertible.toSkeleton_zpow (hL : L.Invertible) (m : ℤ) :
    toSkeleton (hL.zpow m) = ↑(hL.toUnit ^ m) := by
  obtain n | n := m
  · rw [Invertible.zpow_ofNat, Skeleton.toSkeleton_tensorPow, Int.ofNat_eq_natCast,
      _root_.zpow_natCast, Units.val_pow_eq_pow_val, hL.val_toUnit]
  · have hneg : hL.toUnit ^ (Int.negSucc n) = hL.toUnit⁻¹ ^ (n + 1) := by
      rw [← _root_.zpow_natCast hL.toUnit⁻¹ (n + 1), inv_zpow, ← zpow_neg]
      congr 1
    rw [Invertible.zpow_negSucc, Skeleton.toSkeleton_tensorPow, hL.toSkeleton_inv, hneg,
      Units.val_pow_eq_pow_val]

/-- **An integer tensor power of an invertible sheaf of modules is invertible.** -/
theorem Invertible.invertible_zpow (hL : L.Invertible) (m : ℤ) : (hL.zpow m).Invertible := by
  change IsUnit (toSkeleton (hL.zpow m))
  rw [hL.toSkeleton_zpow]
  exact Units.isUnit _

/-- **Integer tensor powers turn addition of exponents into the tensor product.** -/
noncomputable def Invertible.zpowAddIso (hL : L.Invertible) (m m' : ℤ) :
    hL.zpow (m + m') ≅ hL.zpow m ⊗ hL.zpow m' :=
  isoOfToSkeletonEq (by
    rw [hL.toSkeleton_zpow, Skeleton.toSkeleton_tensorObj, hL.toSkeleton_zpow,
      hL.toSkeleton_zpow, ← Units.val_mul, zpow_add])

/-- **The zeroth integer tensor power is the structure sheaf.** -/
noncomputable def Invertible.zpowZeroIso (hL : L.Invertible) :
    hL.zpow 0 ≅ unit X.ringCatSheaf :=
  Scheme.Modules.tensorUnitIsoUnit X

/-- The first integer tensor power is `L` itself. -/
noncomputable def Invertible.zpowOneIso (hL : L.Invertible) : hL.zpow 1 ≅ L :=
  tensorPowOneIso L

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {L : X.Modules}

/-- The class of an integer tensor power in the Picard group is the corresponding power of the
class. -/
@[simp]
theorem Pic.mk_zpow (hL : L.Invertible) (m : ℤ) :
    Pic.mk (hL.zpow m) (hL.invertible_zpow m) = Pic.mk L hL ^ m := by
  change (hL.invertible_zpow m).unit = hL.unit ^ m
  rw [← Units.val_inj, IsUnit.unit_spec]
  exact hL.toSkeleton_zpow m

namespace Modules

/-- On an open subset trivialising the invertible sheaf `L`, the restriction of `F ⊗ L` is
isomorphic to the restriction of `F`. -/
noncomputable def tensorRestrictIsoOfRestrictIso (F : X.Modules) {U : X.Opens}
    (e : L.restrict U.ι ≅ 𝟙_ U.toScheme.Modules) :
    (F ⊗ L).restrict U.ι ≅ F.restrict U.ι :=
  restrictTensorIso U.ι F L ≪≫ tensorIso (Iso.refl _) e ≪≫ ρ_ _

/-- **Tensoring a coherent sheaf of modules with an invertible one preserves coherence.** -/
theorem isCoherent_tensorObj_of_invertible (F : X.Modules) [F.IsCoherent] (hL : L.Invertible) :
    (F ⊗ L).IsCoherent := by
  choose W hxW hW using fun x : X ↦ hL.exists_restrict_iso_tensorUnit x
  have hWcover : IsOpenCover W :=
    IsOpenCover.mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩)
  obtain ⟨ι, U, r, G, hU, hU', hUle, hG⟩ :=
    exists_isOpenCover_generatingSections_le F W hWcover
  have et : ∀ i, L.restrict (U i).ι ≅ 𝟙_ (U i).toScheme.Modules := fun i ↦
    (restrictRestrictIso L (hUle i)).symm ≪≫
      (restrictFunctor' (X.homOfLE (hUle i))).mapIso (hW (r i)).some ≪≫
        restrictTensorUnitIso (X.homOfLE (hUle i))
  have e : ∀ i, (F ⊗ L).restrict (U i).ι ≅ F.restrict (U i).ι := fun i ↦
    tensorRestrictIsoOfRestrictIso F (et i)
  have hq : (F ⊗ L).IsQuasicoherent :=
    isQuasicoherent_of_isAffineOpenCover _ U hU hU' fun i ↦
      (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso (e i).symm
        inferInstance
  have hf : (F ⊗ L).IsFiniteType :=
    isFiniteType_of_generatingSections _ U hU
      (fun i ↦ SheafOfModules.GeneratingSections.equivOfIso (e i).symm (G i))
      fun i ↦ ⟨(hG i).finite⟩
  constructor

/-- **An integer tensor power of an invertible sheaf of modules is coherent after tensoring a
coherent sheaf with it.** -/
theorem isCoherent_tensorObj_zpow (F : X.Modules) [F.IsCoherent] (hL : L.Invertible) (m : ℤ) :
    (F ⊗ hL.zpow m).IsCoherent :=
  isCoherent_tensorObj_of_invertible F (hL.invertible_zpow m)

/-- The sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` attached to a sheaf of modules `F`, a finite
family `L` of invertible sheaves of modules and an integer vector `m`.

This is the sheaf whose Euler characteristic is the subject of Snapper's theorem. -/
noncomputable def tensorZPow {r : ℕ} (F : X.Modules) {L : Fin r → X.Modules}
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) : X.Modules :=
  Fin.foldr r (fun j N ↦ N ⊗ (hL j).zpow (m j)) F

@[simp]
lemma tensorZPow_zero (F : X.Modules) {L : Fin 0 → X.Modules} (hL : ∀ j, (L j).Invertible)
    (m : Fin 0 → ℤ) : tensorZPow F hL m = F :=
  Fin.foldr_zero _ _

lemma tensorZPow_succ {r : ℕ} (F : X.Modules) {L : Fin (r + 1) → X.Modules}
    (hL : ∀ j, (L j).Invertible) (m : Fin (r + 1) → ℤ) :
    tensorZPow F hL m =
      tensorZPow F (fun j ↦ hL j.succ) (fun j ↦ m j.succ) ⊗ (hL 0).zpow (m 0) := by
  rw [tensorZPow, Fin.foldr_succ]
  rfl

/-- **The sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` is coherent** when `F` is coherent and the `Lⱼ`
are invertible. -/
theorem isCoherent_tensorZPow {r : ℕ} (F : X.Modules) [F.IsCoherent] {L : Fin r → X.Modules}
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) : (tensorZPow F hL m).IsCoherent := by
  induction r with
  | zero => rw [tensorZPow_zero]; infer_instance
  | succ r ih =>
    rw [tensorZPow_succ]
    have : (tensorZPow F (fun j ↦ hL j.succ) fun j ↦ m j.succ).IsCoherent :=
      ih (fun j ↦ hL j.succ) fun j ↦ m j.succ
    exact isCoherent_tensorObj_zpow _ (hL 0) (m 0)

end Modules

end AlgebraicGeometry.Scheme
