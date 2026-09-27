/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ZetaFunction
public import WeilConjectures.ZetaSeries

/-!
# Weil groups of curves over a finite field and their representations

This file sets up the group-theoretic side of the purity theorem for real lisse sheaves on
curves: the Weil group of a curve over a finite field, lisse Weil sheaves in their
description as representations of that group, and the elementary operations on them.

The étale fundamental group of a scheme does not exist in Mathlib, so the geometric
fundamental group `π₁(C)` and the Weil group `W(C₀)` are packaged as *data*
(`AlgebraicGeometry.WeilGroup`) recording exactly the structure that the purity argument
uses: the exact degree sequence `1 → π₁(C) → W(C₀) → ℤ → 0` with `π₁(C)` an open profinite
subgroup, a degree-one lift `frobeniusLift`, and, for every closed point `x` of `C₀`, a local
Frobenius element of degree `e_x = [k(x) : 𝔽_q]`.

Coefficients are `ℚ̄_ℓ = PadicAlgCl l`, and the archimedean comparison is a ring embedding
`ι : ℚ̄_ℓ →+* ℂ`.

## Implementation notes

The curve itself enters through the instance arguments `[Finite K]` and `[IsCurve p]` of
`AlgebraicGeometry.WeilGroup`, so that every statement about a `W : WeilGroup p` carries them;
smoothness and geometric connectedness are extra hypotheses where they are needed. Only closed
points of `C₀` — those of `AlgebraicGeometry.Scheme.finitePoints` — index a local Frobenius,
since `AlgebraicGeometry.Scheme.Hom.degreeOver` has the junk value `0` elsewhere.

What the data of a `WeilGroup` does **not** record is that `ker deg` really is the geometric
fundamental group of `C`: that needs the Galois category of finite étale covers of a scheme
and Mathlib's `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`, neither of which is
available. The propositions of this block quantify over an arbitrary `WeilGroup p`, so they
are not consequences of the recorded data alone; they become so once `WeilGroup` is rebased on
the étale fundamental group. See the implementation notes of
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity`.

## Main definitions

- `AlgebraicGeometry.WeilGroup` : the Weil group of a curve over a finite field.
- `AlgebraicGeometry.WeilGroup.Restriction` : the restriction of Weil groups along a nonempty
  open immersion of curves.
- `AlgebraicGeometry.WeilGroup.IsLisse` : a Weil representation is lisse.
- `AlgebraicGeometry.WeilGroup.constLine` : the constant Weil line `B_b`.
- `AlgebraicGeometry.WeilGroup.tateLine` : the Tate line `ℚ̄_ℓ(n) = B_{q ^ (-n)}`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `sk-d-real-weil`: Weil sheaves and their representations.

The Weil group of a curve `p : C₀ ⟶ Spec 𝔽_q`. It is the preimage of the integer powers of
the geometric Frobenius under `π₁(C₀) → Gal(k / 𝔽_q)`, and comes with the exact degree
sequence `1 → π₁(C) → W(C₀) → ℤ → 0` whose kernel is the profinite geometric fundamental
group `π₁(C)`.

Since the étale fundamental group of a scheme is not available, this is recorded as data:
a topological group `W` with a surjective degree homomorphism to `ℤ` whose kernel is open and
profinite, a chosen degree-one lift `frobeniusLift`, and for every closed point `x` of `C₀` a
local Frobenius element `frobenius x`, well defined up to conjugacy, of degree
`e_x = [k(x) : 𝔽_q]`. -/
structure WeilGroup [Finite K] (p : C ⟶ Spec (.of K)) [IsCurve p] where
  /-- The underlying group `W(C₀)` of the Weil group. -/
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The degree homomorphism `deg : W(C₀) → ℤ`. -/
  deg : carrier →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  deg_surjective : Function.Surjective deg
  /-- The geometric fundamental group `π₁(C) = ker deg` is open; equivalently, `deg` is
  continuous for the discrete topology of `ℤ`. -/
  isOpen_ker : IsOpen (deg.ker : Set carrier)
  /-- The geometric fundamental group `π₁(C) = ker deg` is compact. -/
  compactSpace_ker : CompactSpace (deg.ker : Subgroup carrier)
  /-- The geometric fundamental group `π₁(C) = ker deg` is profinite. -/
  totallyDisconnectedSpace_ker : TotallyDisconnectedSpace (deg.ker : Subgroup carrier)
  /-- A chosen lift of the geometric Frobenius, of degree one. -/
  frobeniusLift : carrier
  /-- The chosen lift has degree one. -/
  deg_frobeniusLift : deg frobeniusLift = Multiplicative.ofAdd 1
  /-- A choice of local Frobenius element at a closed point of `C₀`; it is well defined up to
  conjugacy, so the characteristic polynomials of `sk-d-real-weights` do not depend on it. -/
  frobenius : C.finitePoints → carrier
  /-- The local Frobenius at `x` has degree `e_x = [k(x) : 𝔽_q]`. -/
  deg_frobenius (x : C.finitePoints) :
    deg (frobenius x) = Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)

attribute [instance] WeilGroup.group WeilGroup.topologicalSpace WeilGroup.isTopologicalGroup
  WeilGroup.compactSpace_ker WeilGroup.totallyDisconnectedSpace_ker

namespace WeilGroup

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)

/-- The geometric fundamental group `π₁(C)`, the kernel of the degree homomorphism. -/
protected abbrev geometric : Subgroup W.carrier := W.deg.ker

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.

The restriction of Weil groups along a nonempty open immersion `j : U₀ ↪ C₀` of curves over
`𝔽_q`: a continuous, degree-preserving and surjective homomorphism `W(U₀) → W(C₀)` carrying the
local Frobenius at a closed point `x` of `U₀` to the local Frobenius at its image, up to
conjugacy.

Surjectivity is data rather than a conclusion: `π₁(U) → π₁(C)` is surjective for a nonempty
open of a connected normal curve (`sk-i-real-boundary`), but nothing in the data of two
`AlgebraicGeometry.WeilGroup`s forces an arbitrary degree-preserving homomorphism between them
to be onto. Likewise the compatibility `restrict_frobenius` is what ties `restrict` to `j`;
without it a `Restriction` would say nothing about the geometry. -/
structure Restriction {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)} [IsCurve pU] (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (WU : WeilGroup pU) (WC : WeilGroup p) where
  /-- `j` is a morphism of curves over `𝔽_q`. -/
  comp_eq : j ≫ p = pU
  /-- The restriction map `W(U₀) → W(C₀)` of Weil groups. -/
  restrict : WU.carrier →* WC.carrier
  /-- The restriction map is continuous. -/
  continuous_restrict : Continuous restrict
  /-- The restriction map preserves degrees. -/
  deg_restrict : WC.deg.comp restrict = WU.deg
  /-- The restriction map is surjective, because `π₁(U) → π₁(C)` is. -/
  surjective_restrict : Function.Surjective restrict
  /-- The restriction map carries the local Frobenius at a closed point `x` of `U₀` into the
  Frobenius conjugacy class at the image point of `C₀`. -/
  restrict_frobenius (x : U.finitePoints) (y : C.finitePoints) (hxy : j.base x.1 = y.1) :
    IsConj (WC.frobenius y) (restrict (WU.frobenius x))

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `sk-d-real-weil`: Weil sheaves and their representations.

A `ℚ̄_ℓ`-representation of the Weil group is *lisse* if the geometric subgroup `π₁(C)` acts
continuously, i.e. the matrix coefficients of the restricted representation are continuous in
every basis. By `sk-p-real-integral` this is equivalent, for a finite-dimensional `V`, to the
existence of a model over a finite extension `E/ℚ_ℓ` carrying a `π₁(C)`-stable `𝒪_E`-lattice.

Finite-dimensionality of `V` is not part of this predicate: it is an independent condition,
imposed where it is needed (see `AlgebraicGeometry.WeilGroup.isLisseRep`). -/
structure IsLisse {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) : Prop where
  /-- In every basis, the matrix coefficients of the geometric part of `ρ` are continuous. -/
  continuous_toMatrix {n : ℕ} (b : Module.Basis (Fin n) (PadicAlgCl l) V) (i j : Fin n) :
    Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) i j

/-- Blueprint `sk-d-real-weil`: Weil sheaves and their representations.

Continuity of the matrix coefficients in *one* basis of a finite-dimensional `V` implies
continuity in every basis: a change of basis is a fixed invertible matrix, so it acts on the
matrix coefficients by a fixed polynomial expression. -/
theorem isLisse_iff_exists_basis {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) :
    W.IsLisse l ρ ↔ ∃ (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) V), ∀ i j,
      Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) i j := by
  sorry

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
noncomputable def tateLine (n : ℤ) :
    Representation (PadicAlgCl l) W.carrier (PadicAlgCl l) :=
  W.constLine l (Units.mk0 ((Nat.card K : PadicAlgCl l) ^ (-n))
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')))

end WeilGroup

end AlgebraicGeometry
