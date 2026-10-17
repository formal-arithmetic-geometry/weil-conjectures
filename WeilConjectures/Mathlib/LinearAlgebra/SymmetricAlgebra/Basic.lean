/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Functoriality of the symmetric algebra along semilinear maps

For a ring map `ρ : R →+* S` and a `ρ`-semilinear map `l : M →ₛₗ[ρ] N` from an `R`-module to an
`S`-module, we construct the ring map `SymmetricAlgebra R M →+* SymmetricAlgebra S N` extending
`ρ` and `l` (`SymmetricAlgebra.mapSemilinear`). We show that it is compatible with the
augmentations `SymmetricAlgebra.algebraMapInv`, and that the symmetric algebra commutes with
localization: if `S = R[1/g]` and `N = M[1/g]`, then `SymmetricAlgebra S N` is the localization
of `SymmetricAlgebra R M` away from `g`
(`SymmetricAlgebra.isLocalization_away_mapSemilinear`).
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N]

/-- Two ring maps out of a symmetric algebra agree as soon as they agree on the scalars and on
the generators. -/
theorem ringHom_ext {B : Type*} [Semiring B] {F G : SymmetricAlgebra R M →+* B}
    (h₁ : ∀ r, F (algebraMap R _ r) = G (algebraMap R _ r)) (h₂ : ∀ m, F (ι R M m) = G (ι R M m)) :
    F = G := by
  refine RingHom.ext fun x ↦ ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The ring map `Sym_R M →+* Sym_S N` induced by a ring map `ρ : R →+* S` and a `ρ`-semilinear
map `l : M →ₛₗ[ρ] N`. -/
noncomputable def mapSemilinear {ρ : R →+* S} (l : M →ₛₗ[ρ] N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  letI : Algebra R (SymmetricAlgebra S N) := ((algebraMap S _).comp ρ).toAlgebra
  (lift
    { toFun := fun m ↦ ι S N (l m)
      map_add' := fun m m' ↦ by rw [map_add, map_add]
      map_smul' := fun r m ↦ by
        rw [l.map_smulₛₗ, map_smul, Algebra.smul_def, Algebra.smul_def]
        rfl } : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S N).toRingHom

variable {ρ : R →+* S} (l : M →ₛₗ[ρ] N)

@[simp]
theorem mapSemilinear_algebraMap (r : R) :
    mapSemilinear l (algebraMap R _ r) = algebraMap S _ (ρ r) := by
  let : Algebra R (SymmetricAlgebra S N) := ((algebraMap S _).comp ρ).toAlgebra
  exact AlgHom.commutes _ r

@[simp]
theorem mapSemilinear_ι (m : M) : mapSemilinear l (ι R M m) = ι S N (l m) := by
  let : Algebra R (SymmetricAlgebra S N) := ((algebraMap S _).comp ρ).toAlgebra
  exact lift_ι_apply _ m

theorem mapSemilinear_id : mapSemilinear (LinearMap.id : M →ₗ[R] M) = RingHom.id _ :=
  ringHom_ext (fun r ↦ by simp) fun m ↦ by simp

theorem mapSemilinear_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    {σ : S →+* T} {τ : R →+* T} [RingHomCompTriple ρ σ τ] (l' : N →ₛₗ[σ] P) :
    mapSemilinear (l'.comp l) = (mapSemilinear l').comp (mapSemilinear l) :=
  ringHom_ext (fun r ↦ by simp [RingHomCompTriple.comp_apply]) fun m ↦ by simp

/-- `mapSemilinear` is compatible with the augmentations `Sym_R M → R` and `Sym_S N → S`. -/
theorem algebraMapInv_mapSemilinear :
    (algebraMapInv : SymmetricAlgebra S N →ₐ[S] S).toRingHom.comp (mapSemilinear l) =
      ρ.comp (algebraMapInv : SymmetricAlgebra R M →ₐ[R] R).toRingHom :=
  ringHom_ext (fun r ↦ by simp [algebraMapInv]) fun m ↦ by simp [algebraMapInv]

/-- **The symmetric algebra commutes with localization.** Let `S` be the localization of `R` away
from `g` and let `l : M → N` exhibit the `S`-module `N` as the localization of `M` away from `g`.
Then `Sym_S N` is the localization of `Sym_R M` away from `g`. -/
theorem isLocalization_away_mapSemilinear [Algebra R S] (g : R) [IsLocalization.Away g S]
    [Module R N] [IsScalarTower R S N] (l : M →ₗ[R] N) (hl : IsLocalizedModule.Away g l)
    (l' : M →ₛₗ[algebraMap R S] N) (hl' : ∀ m, l' m = l m) :
    letI := (mapSemilinear l').toAlgebra
    IsLocalization.Away (algebraMap R (SymmetricAlgebra R M) g) (SymmetricAlgebra S N) := by
  let := (mapSemilinear l').toAlgebra
  set x := algebraMap R (SymmetricAlgebra R M) g
  have hφ (y : SymmetricAlgebra R M) :
      algebraMap (SymmetricAlgebra R M) (SymmetricAlgebra S N) y = mapSemilinear l' y := rfl
  have hx (n : ℕ) : algebraMap (SymmetricAlgebra R M) (SymmetricAlgebra S N) (x ^ n) =
      algebraMap S _ (algebraMap R S (g ^ n)) := by
    rw [hφ, ← map_pow, mapSemilinear_algebraMap]
  refine ⟨⟨fun ⟨y, n, hn⟩ ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ?_⟩⟩
  · subst hn
    rw [hx]
    rw [map_pow, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := S) g).map
      (algebraMap S (SymmetricAlgebra S N))).pow n
  · -- every element of `Sym_S N` is a fraction with denominator a power of `g`
    induction z using SymmetricAlgebra.induction with
    | algebraMap s =>
      obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) s
      refine ⟨⟨algebraMap R _ r, ⟨x ^ n, n, rfl⟩⟩, ?_⟩
      dsimp only at hr ⊢
      rw [hx, ← map_mul, hr, hφ, mapSemilinear_algebraMap]
    | ι n =>
      obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers g) l n
      refine ⟨⟨ι R M m, ⟨x ^ k, k, rfl⟩⟩, ?_⟩
      dsimp only at hm ⊢
      rw [hx, hφ, mapSemilinear_ι, mul_comm, ← Algebra.smul_def, ← map_smul, algebraMap_smul,
        hl', ← hm, Submonoid.smul_def]
    | mul a b ha hb =>
      obtain ⟨⟨a', ya⟩, ha⟩ := ha
      obtain ⟨⟨b', yb⟩, hb⟩ := hb
      refine ⟨⟨a' * b', ya * yb⟩, ?_⟩
      dsimp only at ha hb ⊢
      rw [Submonoid.coe_mul, map_mul, map_mul, ← ha, ← hb]
      ring
    | add a b ha hb =>
      obtain ⟨⟨a', ya⟩, ha⟩ := ha
      obtain ⟨⟨b', yb⟩, hb⟩ := hb
      refine ⟨⟨a' * yb + b' * ya, ya * yb⟩, ?_⟩
      dsimp only at ha hb ⊢
      rw [Submonoid.coe_mul, map_add, map_mul, map_mul, map_mul, ← ha, ← hb]
      ring
  · -- construct a left inverse `Sym_S N → (Sym_R M)[1/g]`
    let L := Localization.Away x
    have hgL : IsUnit (algebraMap R L g) := by
      rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) L]
      exact IsLocalization.Away.algebraMap_isUnit x
    let : Algebra S L := (IsLocalization.Away.lift g hgL).toAlgebra
    have hSL (s : S) : algebraMap S L s = IsLocalization.Away.lift g hgL s := rfl
    have : IsScalarTower R S L := .of_algebraMap_eq fun r ↦ by
      rw [hSL, IsLocalization.Away.lift_eq]
    let T : M →ₗ[R] L := (IsScalarTower.toAlgHom R (SymmetricAlgebra R M) L).toLinearMap ∘ₗ ι R M
    have hT : ∀ s : Submonoid.powers g, IsUnit (algebraMap R (Module.End R L) s) := by
      rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap R L (g ^ n)) := by rw [map_pow]; exact hgL.pow n
      have hE (a : L) : algebraMap R (Module.End R L) (g ^ n) a = algebraMap R L (g ^ n) * a := by
        rw [Module.algebraMap_end_apply, Algebra.smul_def]
      change IsUnit (algebraMap R (Module.End R L) (g ^ n))
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b hab ↦ hu.mul_left_cancel ?_, fun a ↦ ⟨hu.unit⁻¹ * a, ?_⟩⟩
      · rwa [hE, hE] at hab
      · rw [hE, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    let ψ : N →ₗ[S] L := (IsLocalizedModule.lift (Submonoid.powers g) l T hT)
      |>.extendScalarsOfIsLocalization (Submonoid.powers g) S
    let Ψ : SymmetricAlgebra S N →+* L := (lift ψ).toRingHom
    have hΨ : Ψ.comp (mapSemilinear l') = algebraMap (SymmetricAlgebra R M) L := by
      refine ringHom_ext (fun r ↦ ?_) fun m ↦ ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, mapSemilinear_algebraMap, Ψ,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
        rw [hSL, IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]
      · simp only [RingHom.coe_comp, Function.comp_apply, mapSemilinear_ι, Ψ,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lift_ι_apply, hl', ψ,
          LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply, T]
        rfl
    have h' : algebraMap (SymmetricAlgebra R M) L a = algebraMap (SymmetricAlgebra R M) L b := by
      rw [← hΨ, RingHom.comp_apply, RingHom.comp_apply]
      exact congrArg Ψ h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers x) L).mp h'
    exact ⟨c, hc⟩

end SymmetricAlgebra
