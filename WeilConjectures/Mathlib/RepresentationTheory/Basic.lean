/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The determinant character and the exterior powers of a representation

Two constructions on a monoid representation `ρ : Representation k W V` that Mathlib does not
have, alongside `Representation.tprod` and `Representation.dual`:

* the *determinant character* `δ(w) = det ρ(w)`, a homomorphism `W →* kˣ` (the determinant of
  `ρ w` is a unit because `ρ w` is invertible);
* the representation of `W` on the exterior power `⋀^s V`, by functoriality of `⋀^s`.

## Main declarations

* `Representation.detCharacter`: the determinant character `δ` of a representation.
* `Representation.exteriorPower`: the representation induced on `⋀^s V`.

## Blueprint

`Representation.detCharacter` implements part of `sk-d-weights`.
-/

@[expose] public section

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The *determinant character* of a representation `ρ` is the homomorphism `δ(w) = det ρ(w)`,
valued in the units of `k` because `ρ(w)` is invertible.
(blueprint: `sk-d-weights`) -/
noncomputable def detCharacter (ρ : Representation k W V) : W →* kˣ :=
  (Units.map (LinearMap.det : Module.End k V →* k)).comp (MonoidHom.toHomUnits ρ)

@[simp]
theorem coe_detCharacter_apply (ρ : Representation k W V) (w : W) :
    (ρ.detCharacter w : k) = LinearMap.det (ρ w) :=
  rfl

section Equiv

variable {V' : Type*} [AddCommGroup V'] [Module k V'] {ρ : Representation k W V}
  {σ : Representation k W V'}

/-- An equivalence of representations commutes with the actions. -/
theorem Equiv.apply_apply (e : ρ.Equiv σ) (w : W) (x : V) : e (ρ w x) = σ w (e x) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' w) x

/-- Equivalent representations have the same determinant character. -/
theorem Equiv.detCharacter_eq (e : ρ.Equiv σ) : σ.detCharacter = ρ.detCharacter := by
  ext w
  have : σ w = (e.toLinearEquiv : V →ₗ[k] V') ∘ₗ ρ w ∘ₗ (e.toLinearEquiv.symm : V' →ₗ[k] V) := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      e.toLinearEquiv_apply, e.coe_toIntertwiningMap, e.apply_apply]
    exact congrArg _ (e.toLinearEquiv.apply_symm_apply x).symm
  rw [coe_detCharacter_apply, coe_detCharacter_apply, this, LinearMap.det_conj]

end Equiv

/-- The representation induced on the `s`-th exterior power `⋀^s V`, by functoriality of the
exterior power.  The name shadows the root namespace `exteriorPower`, whose declarations are
therefore spelled `_root_.exteriorPower.*` below. -/
noncomputable def exteriorPower (ρ : Representation k W V) (s : ℕ) :
    Representation k W ↥(⋀[k]^s V) where
  toFun w := _root_.exteriorPower.map s (ρ w)
  map_one' := by
    rw [map_one]
    exact _root_.exteriorPower.map_id
  map_mul' v w := by
    rw [map_mul]
    exact _root_.exteriorPower.map_comp (ρ w) (ρ v)

end Representation
