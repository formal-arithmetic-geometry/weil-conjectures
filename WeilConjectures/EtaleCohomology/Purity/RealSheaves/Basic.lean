/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.ZetaSeries

@[expose] public section

/-!
# Weil groups of curves over a finite field and their representations

This file sets up the group-theoretic side of the purity theorem for real lisse sheaves on
curves: the Weil group of a curve over a finite field, lisse Weil sheaves in their
description as representations of that group, and the elementary operations on them.

The étale fundamental group of a scheme does not exist in Mathlib, so the geometric
fundamental group `π₁(C)` and the Weil group `W(C₀)` are packaged as *data*
(`AlgebraicGeometry.WeilGroup`) recording exactly the structure that the purity argument
uses: the exact degree sequence `1 → π₁(C) → W(C₀) → ℤ → 0` with `π₁(C)` profinite, a
degree-one lift `γ`, and, for every closed point `x` of `C₀`, a local Frobenius element of
degree `e_x = [k(x) : 𝔽_q]`.

Coefficients are `ℚ̄_ℓ = PadicAlgCl l`, and the archimedean comparison is a ring embedding
`ι : ℚ̄_ℓ →+* ℂ`.

## Main definitions

- `AlgebraicGeometry.WeilGroup` : the Weil group of a curve over a finite field.
- `AlgebraicGeometry.WeilGroup.IsLisse` : a Weil representation is lisse.
- `AlgebraicGeometry.WeilGroup.constLine` : the constant Weil line `B_b`.
- `AlgebraicGeometry.WeilGroup.tateLine` : the Tate line `ℚ̄_ℓ(n) = B_{q ^ (-n)}`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}

/-- Blueprint `sk-d-real-weil`: Weil sheaves and their representations.

The Weil group of a curve `p : C₀ ⟶ Spec 𝔽_q`. It is the preimage of the integer powers of
the geometric Frobenius under `π₁(C₀) → Gal(k / 𝔽_q)`, and comes with the exact degree
sequence `1 → π₁(C) → W(C₀) → ℤ → 0` whose kernel is the profinite geometric fundamental
group `π₁(C)`.

Since the étale fundamental group of a scheme is not available, this is recorded as data:
a topological group `W` with a surjective degree homomorphism to `ℤ` whose kernel is
profinite, a chosen degree-one lift `γ`, and for every point `x` of `C₀` a local Frobenius
element `frobenius x`, well defined up to conjugacy, of degree `e_x = [k(x) : 𝔽_q]`. -/
structure WeilGroup (p : C ⟶ Spec (.of K)) where
  /-- The underlying group `W(C₀)` of the Weil group. -/
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The degree homomorphism `deg : W(C₀) → ℤ`. -/
  deg : carrier →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  deg_surjective : Function.Surjective deg
  /-- The geometric fundamental group `π₁(C) = ker deg` is compact. -/
  compactSpace_ker : CompactSpace (deg.ker : Subgroup carrier)
  /-- The geometric fundamental group `π₁(C) = ker deg` is profinite. -/
  totallyDisconnectedSpace_ker : TotallyDisconnectedSpace (deg.ker : Subgroup carrier)
  /-- A chosen lift `γ` of the geometric Frobenius, of degree one. -/
  γ : carrier
  /-- The chosen lift has degree one. -/
  deg_γ : deg γ = Multiplicative.ofAdd 1
  /-- A choice of local Frobenius element at a point of `C₀`; it is well defined up to
  conjugacy, so the characteristic polynomials of `sk-d-real-weights` do not depend on it. -/
  frobenius : C → carrier
  /-- The local Frobenius at `x` has degree `e_x = [k(x) : 𝔽_q]`. -/
  deg_frobenius (x : C) :
    deg (frobenius x) = Multiplicative.ofAdd (p.degreeOver x : ℤ)

attribute [instance] WeilGroup.group WeilGroup.topologicalSpace WeilGroup.isTopologicalGroup
  WeilGroup.compactSpace_ker WeilGroup.totallyDisconnectedSpace_ker

namespace WeilGroup

variable {p : C ⟶ Spec (.of K)} (W : WeilGroup p)

/-- The geometric fundamental group `π₁(C)`, the kernel of the degree homomorphism. -/
protected abbrev geometric : Subgroup W.carrier := W.deg.ker

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `sk-d-real-weil`: Weil sheaves and their representations.

A finite-dimensional `ℚ̄_ℓ`-representation of the Weil group is *lisse* if the geometric
subgroup `π₁(C)` acts continuously, i.e. the matrix coefficients of the restricted
representation are continuous in every basis. By `sk-p-real-integral` this is equivalent to
the existence of a model over a finite extension `E/ℚ_ℓ` carrying a `π₁(C)`-stable
`𝒪_E`-lattice. -/
structure IsLisse {V : Type*} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) : Prop where
  /-- In every basis, the matrix coefficients of the geometric part of `ρ` are continuous. -/
  continuous_toMatrix {n : ℕ} (b : Module.Basis (Fin n) (PadicAlgCl l) V) (i j : Fin n) :
    Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) i j

variable {W}

/-- Blueprint `sk-d-real-operations`: Operations, constituents and coinvariants.

The constant Weil line `B_b`: the one-dimensional representation of `W(C₀)` on which `g`
acts by `b ^ deg g`. -/
noncomputable def constLine (b : (PadicAlgCl l)ˣ) :
    Representation (PadicAlgCl l) W.carrier (PadicAlgCl l) where
  toFun g := (b ^ Multiplicative.toAdd (W.deg g) : (PadicAlgCl l)ˣ) • (1 : Module.End _ _)
  map_one' := by simp
  map_mul' g h := by
    have h' : Multiplicative.toAdd (W.deg (g * h))
        = Multiplicative.toAdd (W.deg g) + Multiplicative.toAdd (W.deg h) := by
      rw [map_mul]; rfl
    rw [h', zpow_add]
    ext
    simp [smul_smul, mul_comm]

/-- Blueprint `sk-d-real-operations`: Operations, constituents and coinvariants.

The Tate line `ℚ̄_ℓ(n) = B_{q ^ (-n)}`, on which the geometric Frobenius acts by `q ^ (-n)`. -/
noncomputable def tateLine (W : WeilGroup p) (n : ℤ) :
    Representation (PadicAlgCl l) W.carrier (PadicAlgCl l) :=
  constLine (W := W) l (Units.mk0 ((Nat.card K : PadicAlgCl l) ^ (-n))
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')))

end WeilGroup

end AlgebraicGeometry
