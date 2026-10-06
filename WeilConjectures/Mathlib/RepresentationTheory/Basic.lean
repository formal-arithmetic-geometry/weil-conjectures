/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Basic

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
* `Matrix.GeneralLinearGroup.toRepresentation`: the defining representation of `GL n k` on
  `n → k`.

## Blueprint

`Representation.detCharacter` implements part of `sk-d-weights`.
-/

@[expose] public section

open scoped Matrix

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

namespace Matrix.GeneralLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (k : Type*) [Field k]

/-- The defining representation of `GL n k` on `n → k`, by matrix-vector multiplication. -/
noncomputable def toRepresentation : Representation k (GL n k) (n → k) where
  toFun g := Matrix.toLinAlgEquiv' (g : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

variable {n k}

@[simp]
theorem toRepresentation_apply (g : GL n k) (v : n → k) :
    toRepresentation n k g v = (g : Matrix n n k) *ᵥ v :=
  rfl

end Matrix.GeneralLinearGroup
