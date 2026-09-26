/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Tangent

/-!
# Degree data and their monodromy groups

A *degree datum* is a group `W` with a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one; its kernel is written `P`.  A *represented* degree datum adds a representation
`ρ : W → GL n k`, whose arithmetic and geometric monodromy groups are the Zariski closures
`G = closure ρ(W)` and `H = closure ρ(P)`, with `F = ρ(γ)`.  Nothing here involves a topology on
`W` or a sheaf: the whole setting is the degree datum.

This file collects the definitions and the three propositions about monodromy groups that the
weight arguments rest on: that `H` is normal in `G` and absorbs commutators, the existence of a
positive central pair, and the central–geometric product `G° = Z(G°)° H°`.

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `toRepresentation` and `IsSemisimple`.
* `RepresentedDegreeDatum.AdmissibleChoice`, `RepresentedDegreeDatum.IsPositiveCentralPair`: the
  data producing a positive central pair `(N, z)`.
* `Representation.isSemisimple_comp_subtype_of_normal`,
  `RepresentedDegreeDatum.normal_and_commutator_mem_geometricMonodromy`: normal restriction and
  passage to the closure.
* `RepresentedDegreeDatum.exists_admissibleChoice_and_isPositiveCentralPair`: a positive central
  representative.
* `RepresentedDegreeDatum.identityComponent_eq_centerOf_mul_geometricMonodromy`: the
  central–geometric product.
-/

@[expose] public section

open scoped Matrix Matrix.Zariski Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  A degree datum: a group
`W`, a surjective homomorphism `deg : W → ℤ` and a chosen element `γ` of degree one. -/
structure DegreeDatum (W : Type*) [Group W] where
  /-- The degree homomorphism. -/
  deg : W →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  surjective_deg : Function.Surjective deg
  /-- The chosen element of degree one. -/
  gamma : W
  /-- The chosen element has degree one. -/
  deg_gamma : deg gamma = Multiplicative.ofAdd 1

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  A represented degree datum
adds to a degree datum a representation `ρ : W → GL n k` on `n → k`. -/
structure RepresentedDegreeDatum (W : Type*) [Group W] (n k : Type*) [Fintype n] [DecidableEq n]
    [Field k] extends DegreeDatum W where
  /-- The representation. -/
  rho : W →* GL n k

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable (D : RepresentedDegreeDatum W n k)

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  The subgroup `P = ker deg`
of degree-zero elements. -/
def degreeZero : Subgroup W := D.deg.ker

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  The arithmetic monodromy
group `G = closure ρ(W)`. -/
def arithmeticMonodromy : Subgroup (GL n k) := D.rho.range.zariskiClosure

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  The geometric monodromy
group `H = closure ρ(P)`. -/
def geometricMonodromy : Subgroup (GL n k) := (D.degreeZero.map D.rho).zariskiClosure

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  The Frobenius element
`F = ρ(γ)`. -/
def frobenius : GL n k := D.rho D.gamma

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  The representation of `W`
on `n → k` underlying the datum. -/
noncomputable def toRepresentation : Representation k W (n → k) where
  toFun w := Matrix.toLinAlgEquiv' (D.rho w : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

/-- Blueprint `sk-d-monodromy`: Represented degree data and monodromy.  A datum is *semisimple*
when `n → k` is a semisimple `W`-representation. -/
def IsSemisimple : Prop := Representation.IsSemisimpleRepresentation D.toRepresentation

/-- Blueprint `sk-d-central`: Positive central pairs and their construction.  A *positive central
pair* for the datum is a pair `(N, z)` with `N > 0` and `z ∈ Z(G) ∩ H Fᴺ`. -/
def IsPositiveCentralPair (N : ℕ) (z : GL n k) : Prop :=
  0 < N ∧ z ∈ D.arithmeticMonodromy.centerOf ∧
    ∃ h ∈ D.geometricMonodromy, z = h * D.frobenius ^ N

/-- Blueprint `sk-d-central`: Positive central pairs and their construction.  An *admissible
choice* consists of `m > 0` with a factorisation `Fᵐ = c h`, `c ∈ Z(G°)°` and `h ∈ H°`, together
with a finite list of elements meeting every coset of `G°` in `G` exactly once. -/
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
  /-- The number of components. -/
  r : ℕ
  /-- The coset representatives. -/
  g : Fin r → GL n k
  /-- The representatives lie in `G`. -/
  g_mem : ∀ i, g i ∈ D.arithmeticMonodromy
  /-- Every element of `G` lies in exactly one coset `g i · G°`. -/
  g_exists_unique : ∀ x ∈ D.arithmeticMonodromy,
    ∃! i, (g i)⁻¹ * x ∈ D.arithmeticMonodromy.identityComponent

variable {D}

/-- Blueprint `sk-d-central`: Positive central pairs and their construction.  The degree
`N = m r` of an admissible choice. -/
def AdmissibleChoice.degree (a : D.AdmissibleChoice) : ℕ := a.m * a.r

/-- Blueprint `sk-d-central`: Positive central pairs and their construction.  The central element
`z = ∏ gᵢ c gᵢ⁻¹` of an admissible choice, an ordered product over the coset
representatives. -/
def AdmissibleChoice.centralElement (a : D.AdmissibleChoice) : GL n k :=
  (List.ofFn fun i ↦ a.g i * a.c * (a.g i)⁻¹).prod

end RepresentedDegreeDatum

/-- Blueprint `sk-i-restriction`: Normal restriction and passage to closure.  A finite-dimensional
semisimple representation restricts semisimply to a normal subgroup. -/
theorem Representation.isSemisimple_comp_subtype_of_normal {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hρ : Representation.IsSemisimpleRepresentation ρ) (N : Subgroup G) [N.Normal] :
    Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  sorry

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable [IsAlgClosed k] [CharZero k] (D : RepresentedDegreeDatum W n k)

/-- Blueprint `sk-i-restriction`: Normal restriction and passage to closure.  The geometric
monodromy group is a normal subgroup of the arithmetic one, every commutator of `G` lies in `H`,
and the derived algebra of `Lie G°` lies in `Lie H°`. -/
theorem normal_and_commutator_mem_geometricMonodromy :
    D.geometricMonodromy ≤ D.arithmeticMonodromy ∧
      (∀ g ∈ D.arithmeticMonodromy, ∀ h ∈ D.geometricMonodromy,
        g * h * g⁻¹ ∈ D.geometricMonodromy) ∧
      (∀ a ∈ D.arithmeticMonodromy, ∀ b ∈ D.arithmeticMonodromy,
        a * b * a⁻¹ * b⁻¹ ∈ D.geometricMonodromy) ∧
      (∀ X ∈ D.arithmeticMonodromy.identityComponent.lieAlgebra,
        ∀ Y ∈ D.arithmeticMonodromy.identityComponent.lieAlgebra,
          ⁅X, Y⁆ ∈ D.geometricMonodromy.identityComponent.lieAlgebra) := by
  sorry

/-- Blueprint `sk-p-central`: A positive central representative.  Every semisimple represented
degree datum admits an admissible choice, and the element `z = ∏ gᵢ c gᵢ⁻¹` of degree `N = m r`
constructed from any admissible choice is a positive central pair. -/
theorem exists_admissibleChoice_and_isPositiveCentralPair (hD : D.IsSemisimple) :
    Nonempty D.AdmissibleChoice ∧
      ∀ a : D.AdmissibleChoice, D.IsPositiveCentralPair a.degree a.centralElement := by
  sorry

/-- Blueprint `sk-p-product`: The central–geometric product.  For a semisimple represented degree
datum the identity component of the arithmetic monodromy group factors as `G° = Z(G°)° H°`. -/
theorem identityComponent_eq_centerOf_mul_geometricMonodromy (hD : D.IsSemisimple) :
    (D.arithmeticMonodromy.identityComponent : Set (GL n k)) =
      ((D.arithmeticMonodromy.identityComponent.centerOf).identityComponent : Set (GL n k)) *
        (D.geometricMonodromy.identityComponent : Set (GL n k)) := by
  sorry

end RepresentedDegreeDatum
