/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Lie
public import WeilConjectures.Mathlib.RepresentationTheory.Semisimple

/-!
# Degree data and their monodromy groups

A *degree datum* is a group `W` with a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one; its kernel is written `P`.  A *represented* degree datum adds a representation
`ρ : W → GL n k`, whose arithmetic and geometric monodromy groups are the Zariski closures
`G = closure ρ(W)` and `H = closure ρ(P)`, with `F = ρ(γ)`.  Nothing here involves a topology on
`W` or a sheaf: the whole setting is the degree datum.

The groups `G` and `H` are closed subgroup schemes of `GL_n`, given by their Hopf ideals
`Matrix.GeneralLinearGroup.vanishingIdeal` in `Matrix.GeneralLinearGroup.CoordinateRing n k`.
Their groups of points, identity components, centres and Lie algebras are
`Matrix.GeneralLinearGroup.zeroLocus`, `identityComponent`, `center` and `lieAlgebra`.

This file collects the definitions and the propositions about monodromy groups that the weight
arguments rest on: that `H` is normal in `G` and absorbs commutators, the existence of a positive
central pair, and the central–geometric product `G° = Z(G°)° H°`.

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `asRepresentation` and `IsSemisimple`.
* `RepresentedDegreeDatum.AdmissibleChoice`, `RepresentedDegreeDatum.IsPositiveCentralPair`: the
  data producing a positive central pair `(N, z)`.
* `RepresentedDegreeDatum.arithmeticMonodromy_le_geometricMonodromy`,
  `RepresentedDegreeDatum.geometricMonodromy_subgroupOf_normal`,
  `RepresentedDegreeDatum.commutator_le_geometricMonodromy`,
  `RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`: normal restriction and passage
  to the closure.
* `RepresentedDegreeDatum.exists_admissibleChoice`,
  `RepresentedDegreeDatum.isPositiveCentralPair_centralElement`: a positive central
  representative.
* `RepresentedDegreeDatum.identityComponent_eq_center_mul_geometricMonodromy`: the
  central–geometric product.

## Blueprint

`DegreeDatum`, `RepresentedDegreeDatum` and the attached definitions, among them
`RepresentedDegreeDatum.arithmeticMonodromy` and `RepresentedDegreeDatum.geometricMonodromy`,
implement `sk-d-monodromy`;
`RepresentedDegreeDatum.AdmissibleChoice` and `RepresentedDegreeDatum.IsPositiveCentralPair`
implement `sk-d-central`;
`RepresentedDegreeDatum.arithmeticMonodromy_le_geometricMonodromy`,
`RepresentedDegreeDatum.geometricMonodromy_subgroupOf_normal`,
`RepresentedDegreeDatum.commutator_le_geometricMonodromy` and
`RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy` implement `sk-i-restriction`,
together with `Matrix.GeneralLinearGroup.instIsHopfIdealVanishingIdeal` and
`Representation.isSemisimpleRepresentation_comp_subtype`;
`RepresentedDegreeDatum.exists_admissibleChoice` and
`RepresentedDegreeDatum.isPositiveCentralPair_centralElement` implement `sk-p-central`;
`RepresentedDegreeDatum.identityComponent_eq_center_mul_geometricMonodromy` implements
`sk-p-product`.
-/

@[expose] public section

universe u

open scoped Matrix Pointwise
open Matrix.GeneralLinearGroup

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

/-- The arithmetic monodromy group `G = closure ρ(W)`, as a closed subgroup scheme of `GL_n`: the
Hopf ideal of equations vanishing on `ρ(W)`, which cuts out the reduced Zariski closure.
(blueprint: `sk-d-monodromy`) -/
noncomputable def arithmeticMonodromy : Ideal (CoordinateRing n k) :=
  vanishingIdeal (D.rep.range : Set (GL n k))

/-- The geometric monodromy group `H = closure ρ(P)`, as a closed subgroup scheme of `GL_n`: the
Hopf ideal of equations vanishing on `ρ(P)`, which cuts out the reduced Zariski closure.
(blueprint: `sk-d-monodromy`) -/
noncomputable def geometricMonodromy : Ideal (CoordinateRing n k) :=
  vanishingIdeal (D.degreeZero.map D.rep : Set (GL n k))

instance : D.arithmeticMonodromy.IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

instance : D.geometricMonodromy.IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

/-- The image of the representation lies in the arithmetic monodromy group.
(blueprint: `sk-d-monodromy`) -/
theorem rep_mem_zeroLocus_arithmeticMonodromy (w : W) :
    D.rep w ∈ zeroLocus D.arithmeticMonodromy k :=
  subset_zeroLocus_vanishingIdeal D.rep.range ⟨w, rfl⟩

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

/-- A *positive central pair* for the datum is a pair `(N, z)` with `N > 0` and
`z ∈ Z(G) ∩ H Fᴺ`.
(blueprint: `sk-d-central`) -/
def IsPositiveCentralPair (N : ℕ) (z : GL n k) : Prop :=
  0 < N ∧ z ∈ zeroLocus (center D.arithmeticMonodromy) k ∧
    ∃ h ∈ zeroLocus D.geometricMonodromy k, z = h * D.frobenius ^ N

-- The identity component `G°` is a closed subgroup scheme over an algebraically closed field.
variable [IsAlgClosed k]

/-- The number of connected components of the arithmetic monodromy group: the index of `G°(k)`
in `G(k)`.
(blueprint: `sk-d-central`) -/
noncomputable def componentCount : ℕ :=
  ((zeroLocus (identityComponent D.arithmeticMonodromy) k).subgroupOf
    (zeroLocus D.arithmeticMonodromy k)).index

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
  c_mem : c ∈ zeroLocus (identityComponent (center (identityComponent D.arithmeticMonodromy))) k
  /-- The geometric factor lies in `H°`. -/
  h_mem : h ∈ zeroLocus (identityComponent D.geometricMonodromy) k
  /-- The factorisation of `Fᵐ`. -/
  frobenius_pow_eq : D.frobenius ^ m = c * h
  /-- The coset representatives. -/
  g : Fin D.componentCount → GL n k
  /-- The representatives lie in `G`. -/
  g_mem : ∀ i, g i ∈ zeroLocus D.arithmeticMonodromy k
  /-- Every element of `G` lies in exactly one coset `g i · G°`. -/
  g_exists_unique : ∀ x ∈ zeroLocus D.arithmeticMonodromy k,
    ∃! i, (g i)⁻¹ * x ∈ zeroLocus (identityComponent D.arithmeticMonodromy) k

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

/-- The geometric monodromy group is contained in the arithmetic one: `H ⊆ G`, so the ideal of `G`
is contained in the ideal of `H`.
(blueprint: `sk-i-restriction`) -/
theorem arithmeticMonodromy_le_geometricMonodromy :
    D.arithmeticMonodromy ≤ D.geometricMonodromy :=
  vanishingIdeal_anti (Subgroup.map_le_range D.rep D.degreeZero)

/-- The geometric monodromy group is a normal subgroup scheme of the arithmetic one: for every
`k`-algebra `R`, the `R`-points of `H` form a normal subgroup of the `R`-points of `G`.
(blueprint: `sk-i-restriction`) -/
instance geometricMonodromy_subgroupOf_normal (R : Type*) [CommRing R] [Algebra k R] :
    ((zeroLocus D.geometricMonodromy R).subgroupOf (zeroLocus D.arithmeticMonodromy R)).Normal := by
  sorry

/-- Every commutator of the arithmetic monodromy group lies in the geometric one.
(blueprint: `sk-i-restriction`) -/
theorem commutator_le_geometricMonodromy :
    ⁅zeroLocus D.arithmeticMonodromy k, zeroLocus D.arithmeticMonodromy k⁆ ≤
      zeroLocus D.geometricMonodromy k := by
  sorry

variable [IsAlgClosed k] [CharZero k]

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
group factors as `G° = Z(G°)° H°` on `k`-points.
(blueprint: `sk-p-product`) -/
theorem identityComponent_eq_center_mul_geometricMonodromy (hD : D.IsSemisimple) :
    (zeroLocus (identityComponent D.arithmeticMonodromy) k : Set (GL n k)) =
      (zeroLocus (identityComponent (center (identityComponent D.arithmeticMonodromy))) k :
          Set (GL n k)) *
        (zeroLocus (identityComponent D.geometricMonodromy) k : Set (GL n k)) := by
  sorry

end RepresentedDegreeDatum

namespace RepresentedDegreeDatum

-- `LieRing.ofAssociativeRing` is the commutator bracket of the matrix ring, as in
-- `WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Lie`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {W : Type*} [Group W] {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
variable (D : RepresentedDegreeDatum W n k) [IsAlgClosed k] [CharZero k]

/-- The derived algebra of `Lie G°` lies in `Lie H°`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_lieAlgebra_geometricMonodromy {X Y : Matrix n n k}
    (hX : X ∈ lieAlgebra (identityComponent D.arithmeticMonodromy))
    (hY : Y ∈ lieAlgebra (identityComponent D.arithmeticMonodromy)) :
    ⁅X, Y⁆ ∈ lieAlgebra (identityComponent D.geometricMonodromy) := by
  sorry

end RepresentedDegreeDatum
