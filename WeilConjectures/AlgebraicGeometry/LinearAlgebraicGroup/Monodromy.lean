/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Tangent
public import WeilConjectures.Mathlib.RepresentationTheory.Semisimple

/-!
# Degree data and their monodromy groups

A *degree datum* is a group `W` with a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one; its kernel is written `P`.  A *represented* degree datum adds a representation
`ρ : W → GL n k`, whose arithmetic and geometric monodromy groups are the Zariski closures
`G = closure ρ(W)` and `H = closure ρ(P)`, with `F = ρ(γ)`.  Nothing here involves a topology on
`W` or a sheaf: the whole setting is the degree datum.

This file collects the definitions and the propositions about monodromy groups that the weight
arguments rest on: that `H` is normal in `G` and absorbs commutators, the existence of a positive
central pair, and the central–geometric product `G° = Z(G°)° H°`.

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `asRepresentation` and `IsSemisimple`.
* `RepresentedDegreeDatum.AdmissibleChoice`, `RepresentedDegreeDatum.IsPositiveCentralPair`: the
  data producing a positive central pair `(N, z)`.
* `RepresentedDegreeDatum.geometricMonodromy_le_arithmeticMonodromy`,
  `RepresentedDegreeDatum.geometricMonodromy_subgroupOf_normal`,
  `RepresentedDegreeDatum.commutator_le_geometricMonodromy`,
  `RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`: normal restriction and passage
  to the closure.
* `RepresentedDegreeDatum.exists_admissibleChoice`,
  `RepresentedDegreeDatum.isPositiveCentralPair_centralElement`: a positive central
  representative.
* `RepresentedDegreeDatum.identityComponent_eq_centerOf_mul_geometricMonodromy`: the
  central–geometric product.

## Blueprint

`DegreeDatum`, `RepresentedDegreeDatum` and the attached definitions implement `sk-d-monodromy`;
`RepresentedDegreeDatum.AdmissibleChoice` and `RepresentedDegreeDatum.IsPositiveCentralPair`
implement `sk-d-central`;
`RepresentedDegreeDatum.geometricMonodromy_le_arithmeticMonodromy`,
`RepresentedDegreeDatum.geometricMonodromy_subgroupOf_normal`,
`RepresentedDegreeDatum.commutator_le_geometricMonodromy` and
`RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy` implement `sk-i-restriction`;
`RepresentedDegreeDatum.exists_admissibleChoice` and
`RepresentedDegreeDatum.isPositiveCentralPair_centralElement` implement `sk-p-central`;
`RepresentedDegreeDatum.identityComponent_eq_centerOf_mul_geometricMonodromy` implements
`sk-p-product`.
-/

@[expose] public section

open scoped Matrix Zariski Pointwise

-- `LieRing.ofAssociativeRing` is the commutator bracket of the matrix ring; see the comment in
-- `WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Tangent`.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A degree datum: a group `W`, a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one.
(blueprint: `sk-d-monodromy`) -/
structure DegreeDatum (W : Type*) [Group W] where
  /-- The degree homomorphism. -/
  deg : W →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  surjective_deg : Function.Surjective deg
  /-- The chosen element of degree one. -/
  degreeOneElement : W
  /-- The chosen element has degree one. -/
  deg_degreeOneElement : deg degreeOneElement = Multiplicative.ofAdd 1

/-- A represented degree datum adds to a degree datum a representation `ρ : W → GL n k` on
`n → k`.
(blueprint: `sk-d-monodromy`) -/
structure RepresentedDegreeDatum (W : Type*) [Group W] (n k : Type*) [Fintype n] [DecidableEq n]
    [Field k] extends DegreeDatum W where
  /-- The representation. -/
  rep : W →* GL n k

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable (D : RepresentedDegreeDatum W n k)

/-- The subgroup `P = ker deg` of degree-zero elements.
(blueprint: `sk-d-monodromy`) -/
def degreeZero : Subgroup W := D.deg.ker

/-- The arithmetic monodromy group `G = closure ρ(W)`.
(blueprint: `sk-d-monodromy`) -/
def arithmeticMonodromy : Subgroup (GL n k) := D.rep.range.zariskiClosure

/-- The geometric monodromy group `H = closure ρ(P)`.
(blueprint: `sk-d-monodromy`) -/
def geometricMonodromy : Subgroup (GL n k) := (D.degreeZero.map D.rep).zariskiClosure

/-- The Frobenius element `F = ρ(γ)`.
(blueprint: `sk-d-monodromy`) -/
def frobenius : GL n k := D.rep D.degreeOneElement

/-- The representation of `W` on `n → k` underlying the datum.
(blueprint: `sk-d-monodromy`) -/
noncomputable def asRepresentation : Representation k W (n → k) where
  toFun w := Matrix.toLinAlgEquiv' (D.rep w : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

/-- A datum is *semisimple* when `n → k` is a semisimple `W`-representation.  This is an `abbrev`
so that the underlying class `Representation.IsSemisimpleRepresentation` stays visible to
instance search.
(blueprint: `sk-d-monodromy`) -/
noncomputable abbrev IsSemisimple : Prop :=
  Representation.IsSemisimpleRepresentation D.asRepresentation

/-- The number of connected components of the arithmetic monodromy group: the index of `G°`
in `G`. -/
noncomputable def componentCount : ℕ :=
  (D.arithmeticMonodromy.identityComponent.subgroupOf D.arithmeticMonodromy).index

/-- A *positive central pair* for the datum is a pair `(N, z)` with `N > 0` and
`z ∈ Z(G) ∩ H Fᴺ`.
(blueprint: `sk-d-central`) -/
def IsPositiveCentralPair (N : ℕ) (z : GL n k) : Prop :=
  0 < N ∧ z ∈ D.arithmeticMonodromy.centerOf ∧
    ∃ h ∈ D.geometricMonodromy, z = h * D.frobenius ^ N

/-- An *admissible choice* consists of `m > 0` with a factorisation `Fᵐ = c h`, `c ∈ Z(G°)°` and
`h ∈ H°`, together with a family of elements meeting every coset of `G°` in `G` exactly once,
indexed by the number `Fin D.componentCount` of those cosets.
(blueprint: `sk-d-central`) -/
structure AdmissibleChoice where
  /-- The exponent `m > 0`. -/
  m : ℕ
  /-- Positivity of the exponent. -/
  m_pos : 0 < m
  /-- The central factor `c ∈ Z(G°)°`. -/
  c : GL n k
  /-- The geometric factor `h ∈ H°`. -/
  h : GL n k
  /-- The central factor lies in `Z(G°)°`. -/
  c_mem : c ∈ (D.arithmeticMonodromy.identityComponent.centerOf).identityComponent
  /-- The geometric factor lies in `H°`. -/
  h_mem : h ∈ D.geometricMonodromy.identityComponent
  /-- The factorisation of `Fᵐ`. -/
  frobenius_pow_eq : D.frobenius ^ m = c * h
  /-- The coset representatives. -/
  g : Fin D.componentCount → GL n k
  /-- The representatives lie in `G`. -/
  g_mem : ∀ i, g i ∈ D.arithmeticMonodromy
  /-- Every element of `G` lies in exactly one coset `g i · G°`. -/
  g_exists_unique : ∀ x ∈ D.arithmeticMonodromy,
    ∃! i, (g i)⁻¹ * x ∈ D.arithmeticMonodromy.identityComponent

variable {D}

/-- The degree `N = m r` of an admissible choice, where `r` is the number of connected components
of `G`.
(blueprint: `sk-d-central`) -/
noncomputable def AdmissibleChoice.degree (a : D.AdmissibleChoice) : ℕ := a.m * D.componentCount

/-- The central element `z = ∏ gᵢ c gᵢ⁻¹` of an admissible choice, an ordered product over the
coset representatives.
(blueprint: `sk-d-central`) -/
noncomputable def AdmissibleChoice.centralElement (a : D.AdmissibleChoice) : GL n k :=
  (List.ofFn fun i ↦ a.g i * a.c * (a.g i)⁻¹).prod

end RepresentedDegreeDatum

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable (D : RepresentedDegreeDatum W n k)

/-- The geometric monodromy group is contained in the arithmetic one.
(blueprint: `sk-i-restriction`) -/
theorem geometricMonodromy_le_arithmeticMonodromy :
    D.geometricMonodromy ≤ D.arithmeticMonodromy := by
  sorry

/-- The geometric monodromy group is normal in the arithmetic one.
(blueprint: `sk-i-restriction`) -/
instance geometricMonodromy_subgroupOf_normal :
    (D.geometricMonodromy.subgroupOf D.arithmeticMonodromy).Normal := by
  sorry

/-- Every commutator of the arithmetic monodromy group lies in the geometric one.
(blueprint: `sk-i-restriction`) -/
theorem commutator_le_geometricMonodromy :
    ⁅D.arithmeticMonodromy, D.arithmeticMonodromy⁆ ≤ D.geometricMonodromy := by
  sorry

variable [IsAlgClosed k] [CharZero k]

/-- The derived algebra of `Lie G°` lies in `Lie H°`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_lieAlgebra_geometricMonodromy {X Y : Matrix n n k}
    (hX : X ∈ D.arithmeticMonodromy.identityComponent.lieAlgebra)
    (hY : Y ∈ D.arithmeticMonodromy.identityComponent.lieAlgebra) :
    ⁅X, Y⁆ ∈ D.geometricMonodromy.identityComponent.lieAlgebra := by
  sorry

/-- Every semisimple represented degree datum admits an admissible choice.
(blueprint: `sk-p-central`) -/
theorem exists_admissibleChoice (hD : D.IsSemisimple) : Nonempty D.AdmissibleChoice := by
  sorry

/-- The element `z = ∏ gᵢ c gᵢ⁻¹` of degree `N = m r` constructed from an admissible choice is a
positive central pair.
(blueprint: `sk-p-central`) -/
theorem isPositiveCentralPair_centralElement (a : D.AdmissibleChoice) :
    D.IsPositiveCentralPair a.degree a.centralElement := by
  sorry

/-- For a semisimple represented degree datum the identity component of the arithmetic monodromy
group factors as `G° = Z(G°)° H°`.
(blueprint: `sk-p-product`) -/
theorem identityComponent_eq_centerOf_mul_geometricMonodromy (hD : D.IsSemisimple) :
    (D.arithmeticMonodromy.identityComponent : Set (GL n k)) =
      ((D.arithmeticMonodromy.identityComponent.centerOf).identityComponent : Set (GL n k)) *
        (D.geometricMonodromy.identityComponent : Set (GL n k)) := by
  sorry

end RepresentedDegreeDatum
