/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Cardinality

/-! The ordinary algebraic resolution underlying the finite point resolution. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 1000000 in
set_option profiler true in
-- The finite-presentation and PID elaboration needs a larger heartbeat budget.
/-- A finite integral algebra admits an equal-rank ordinary free resolution.

Source: the finite free and finitely presented coefficient extension paragraph of the
scalar-six direct-image proof (blueprint: lem-s3-integral-finite-point-resolution-algebraic).

The proof chooses a finite free presentation over the DVR, proves that its kernel is finite
free, and uses the nonzero ell-power annihilator of the target to compare the two ranks. -/
theorem integralFinitePointResolution_algebraic
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (φ : PadicAlgCl.integers ell E.1 →+* A) :
    letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
    let φ' : PadicAlgCl.integers ell E.1 →+* ULift.{u + 1} A :=
      ULift.ringEquiv.symm.toRingHom.comp φ
    letI : Module (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A) :=
      Module.compHom (ULift.{u + 1} A) φ'
    ∃ (r : ℕ)
      (f : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
        ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
          ULift.{u + 1} (PadicAlgCl.integers ell E.1)))
      (g : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
        ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A)),
      Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧
        Function.Surjective g.hom := by
  classical
  dsimp only
  let R := PadicAlgCl.integers ell E.1
  letI : Module R A := Module.compHom A φ
  let φ' : R →+* ULift.{u + 1} A := ULift.ringEquiv.symm.toRingHom.comp φ
  letI : Module R (ULift.{u + 1} A) := Module.compHom (ULift.{u + 1} A) φ'
  obtain ⟨r, g, hg⟩ := Module.Finite.exists_fin' R (ULift.{u + 1} A)
  let K := LinearMap.ker g
  obtain ⟨s, ⟨b⟩⟩ := K.nonempty_basis_of_pid (Pi.basisFun R (Fin r))
  letI := Module.Finite.of_basis b
  obtain ⟨n, hn⟩ := hA
  let t : R := (ell ^ n : ℕ)
  have ht : t ≠ 0 := by
    have hpow : (ell ^ n : ℕ) ≠ 0 := pow_ne_zero n (Fact.out : ell.Prime).ne_zero
    change ((ell ^ n : ℕ) : R) ≠ 0
    exact Nat.cast_ne_zero.mpr hpow
  have hkill (a : ULift.{u + 1} A) : t • a = 0 := by
    rw [show t = ((ell ^ n : ℕ) : R) from rfl, Nat.cast_smul_eq_nsmul]
    exact ULift.ext (hn a.down)
  let j : (Fin r → R) →ₗ[R] K :=
    (t • (LinearMap.id : (Fin r → R) →ₗ[R] (Fin r → R))).codRestrict K
      (fun x ↦ by
        change g (t • x) = 0
        rw [map_smul]
        exact hkill (g x))
  have hj : Function.Injective j := by
    intro x y h
    have h' : t • x = t • y := congrArg Subtype.val h
    exact (smul_right_injective _ ht) h'
  have hs : s = r := by
    have h₁ := LinearMap.finrank_le_finrank_of_injective K.subtype_injective
    have h₂ := LinearMap.finrank_le_finrank_of_injective hj
    have hb : Module.finrank R K = s := by
      simpa using Module.finrank_eq_card_basis b
    have hr : Module.finrank R (Fin r → R) = r := by
      simp
    exact Nat.le_antisymm (by simpa [hb, hr] using h₁) (by simpa [hb, hr] using h₂)
  subst s
  let e : (Fin r → ULift.{u + 1} R) ≃ₗ[R] (Fin r → R) :=
    LinearEquiv.piCongrRight (fun _ ↦ ULift.moduleEquiv)
  let k : (Fin r → R) ≃ₗ[R] K := b.equivFun.symm
  let f := e.symm.toLinearMap.comp (K.subtype.comp (k.toLinearMap.comp e.toLinearMap))
  let g' := g.comp e.toLinearMap
  refine ⟨r, ModuleCat.ofHom f, ModuleCat.ofHom g', ?_, ?_, ?_⟩
  · exact e.symm.injective.comp (K.subtype_injective.comp (k.injective.comp e.injective))
  · intro x
    constructor
    · intro hx
      let y : K := ⟨e x, hx⟩
      refine ⟨e.symm (k.symm y), ?_⟩
      change e.symm (K.subtype (k (e (e.symm (k.symm y))))) = x
      simp [y]
    · rintro ⟨y, rfl⟩
      change g (e (e.symm (K.subtype (k (e y))))) = 0
      simp only [LinearEquiv.apply_symm_apply]
      exact (k (e y)).property
  · exact hg.comp e.surjective

end AlgebraicGeometry.ProEtale.CondensedRing
