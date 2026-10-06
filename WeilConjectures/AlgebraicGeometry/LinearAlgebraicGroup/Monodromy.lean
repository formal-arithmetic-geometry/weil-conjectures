/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Geometry
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
Their groups of points, identity components, centers and Lie algebras are
`Matrix.GeneralLinearGroup.zeroLocus`, `identityComponent`, `center` and `lieAlgebra`.

This file collects the definitions and the propositions about monodromy groups that the weight
arguments rest on: that `H` is normal in `G` and absorbs commutators, the existence of a positive
central pair, and the central–geometric product `G° = Z(G°)° H°`. The normality and commutator
statements are instances of general facts about Zariski closures of subgroups of `GL n k`
(`Matrix.GeneralLinearGroup.zeroLocus_vanishingIdeal_le_normalizer` and
`Matrix.GeneralLinearGroup.commutator_zeroLocus_vanishingIdeal_le`).

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `asRepresentation` and `IsSemisimple`.
* `RepresentedDegreeDatum.AdmissibleChoice`, `RepresentedDegreeDatum.IsPositiveCentralPair`: the
  data producing a positive central pair `(N, z)`.
* `RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
  `RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`: normal restriction and passage
  to the closure.
* `RepresentedDegreeDatum.isSemisimpleRepresentation_degreeZero`,
  `RepresentedDegreeDatum.isSemisimpleRepresentation_arithmeticMonodromy`,
  `RepresentedDegreeDatum.isSemisimpleRepresentation_identityComponent_arithmeticMonodromy`: a
  semisimple datum is semisimple for `P`, for `G` and for `G°`.
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
`RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
`RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
`RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
`RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy` and
`RepresentedDegreeDatum.lie_mem_lieAlgebra_identityComponent_geometricMonodromy` implement
`sk-i-restriction`, the last four also `lem-ag-closure-commutators`;
`RepresentedDegreeDatum.isSemisimpleRepresentation_degreeZero` implements
`lem-mg-normal-restriction-semisimple`;
`RepresentedDegreeDatum.isSemisimpleRepresentation_arithmeticMonodromy` and
`RepresentedDegreeDatum.isSemisimpleRepresentation_identityComponent_arithmeticMonodromy` implement
`lem-ag-closure-semisimple`;
`RepresentedDegreeDatum.exists_admissibleChoice` and
`RepresentedDegreeDatum.isPositiveCentralPair_centralElement` implement `sk-p-central`;
`RepresentedDegreeDatum.identityComponent_eq_center_mul_geometricMonodromy` implements
`sk-p-product`.
-/

@[expose] public section

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

instance : D.degreeZero.Normal :=
  D.deg.normal_ker

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
  inferInstanceAs ((vanishingIdeal (D.rep.range : Set (GL n k))).IsHopfIdeal k)

instance : D.geometricMonodromy.IsHopfIdeal k :=
  inferInstanceAs ((vanishingIdeal (D.degreeZero.map D.rep : Set (GL n k))).IsHopfIdeal k)

/-- The image `ρ(W)` of the representation lies in the arithmetic monodromy group.
(blueprint: `sk-d-monodromy`) -/
theorem range_rep_le_zeroLocus_arithmeticMonodromy :
    D.rep.range ≤ zeroLocus D.arithmeticMonodromy k :=
  subset_zeroLocus_vanishingIdeal D.rep.range

/-- The image `ρ(P)` of the degree-zero subgroup lies in the geometric monodromy group.
(blueprint: `sk-d-monodromy`) -/
theorem map_rep_degreeZero_le_zeroLocus_geometricMonodromy :
    D.degreeZero.map D.rep ≤ zeroLocus D.geometricMonodromy k :=
  subset_zeroLocus_vanishingIdeal (D.degreeZero.map D.rep)

theorem rep_mem_zeroLocus_arithmeticMonodromy (w : W) :
    D.rep w ∈ zeroLocus D.arithmeticMonodromy k :=
  D.range_rep_le_zeroLocus_arithmeticMonodromy ⟨w, rfl⟩

theorem rep_mem_zeroLocus_geometricMonodromy {w : W} (hw : w ∈ D.degreeZero) :
    D.rep w ∈ zeroLocus D.geometricMonodromy k :=
  D.map_rep_degreeZero_le_zeroLocus_geometricMonodromy ⟨w, hw, rfl⟩

/-- The Frobenius element `F = ρ(γ)`.
(blueprint: `sk-d-monodromy`) -/
def frobenius : GL n k := D.rep D.degreeOneElement

/-- The representation of `W` on `n → k` underlying the datum.
(blueprint: `sk-d-monodromy`) -/
noncomputable def asRepresentation : Representation k W (n → k) where
  toFun w := Matrix.toLinAlgEquiv' (D.rep w : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

theorem asRepresentation_eq : D.asRepresentation = (toRepresentation n k).comp D.rep :=
  rfl

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

/-- The ideal of `G` is contained in the ideal of `H`; that is, `H ⊆ G` as closed subschemes of
`GL_n`.
(blueprint: `sk-i-restriction`) -/
theorem arithmeticMonodromy_le_geometricMonodromy :
    D.arithmeticMonodromy ≤ D.geometricMonodromy :=
  vanishingIdeal_anti (Subgroup.map_le_range D.rep D.degreeZero)

/-- The geometric monodromy group is contained in the arithmetic one: `H(R) ⊆ G(R)` for every
`k`-algebra `R`.
(blueprint: `sk-i-restriction`) -/
theorem zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy (R : Type*) [CommRing R]
    [Algebra k R] : zeroLocus D.geometricMonodromy R ≤ zeroLocus D.arithmeticMonodromy R :=
  zeroLocus_anti D.arithmeticMonodromy_le_geometricMonodromy

/-- The geometric monodromy group is a normal subgroup scheme of the arithmetic one: for every
`k`-algebra `R`, the `R`-points of `H` form a normal subgroup of the `R`-points of `G`. This is the
closure of the normality of `ρ(P)` in `ρ(W)`.
(blueprint: `sk-i-restriction`, `lem-ag-closure-commutators`) -/
theorem normal_zeroLocus_geometricMonodromy (R : Type*) [CommRing R] [Algebra k R] :
    ((zeroLocus D.geometricMonodromy R).subgroupOf (zeroLocus D.arithmeticMonodromy R)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy R)]
  refine zeroLocus_vanishingIdeal_le_normalizer (Γ := D.rep.range) (Δ := D.degreeZero.map D.rep)
    ?_ R
  have : D.degreeZero.Normal := D.deg.normal_ker
  rw [MonoidHom.range_eq_map, ← Subgroup.normalizer_eq_top_iff.2 this]
  exact Subgroup.le_normalizer_map D.rep

open scoped commutatorElement in
/-- Every commutator of the arithmetic monodromy group lies in the geometric one: for every
`k`-algebra `R`, `⁅G(R), G(R)⁆ ⊆ H(R)`. This is the closure of `⁅ρ(W), ρ(W)⁆ ⊆ ρ(P)`, which holds
because `W ⧸ P ≅ ℤ` is abelian.
(blueprint: `sk-i-restriction`, `lem-ag-closure-commutators`) -/
theorem commutator_zeroLocus_le_zeroLocus_geometricMonodromy (R : Type*) [CommRing R]
    [Algebra k R] :
    ⁅zeroLocus D.arithmeticMonodromy R, zeroLocus D.arithmeticMonodromy R⁆ ≤
      zeroLocus D.geometricMonodromy R := by
  refine commutator_zeroLocus_vanishingIdeal_le (Γ := D.rep.range) (Δ := D.degreeZero.map D.rep)
    ?_ R
  rw [Subgroup.commutator_le]
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩
  exact ⟨⁅w₁, w₂⁆, Abelianization.commutator_subset_ker D.deg
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top w₁) (Subgroup.mem_top w₂)),
    map_commutatorElement D.rep w₁ w₂⟩

section Lie

-- `LieRing.ofAssociativeRing` is the commutator bracket of the matrix ring, as in
-- `WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Lie`.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The derived algebra of `Lie G` lies in `Lie H`, over any field: the bracket comes from the
commutator of `1 + εX` and `1 + δY` over `k[ε, δ]/(ε², δ²)`, which lies in `H` by
`commutator_zeroLocus_le_zeroLocus_geometricMonodromy`.
(blueprint: `sk-i-restriction`, `lem-ag-closure-commutators`) -/
theorem lie_mem_lieAlgebra_geometricMonodromy {X Y : Matrix n n k}
    (hX : X ∈ lieAlgebra D.arithmeticMonodromy) (hY : Y ∈ lieAlgebra D.arithmeticMonodromy) :
    ⁅X, Y⁆ ∈ lieAlgebra D.geometricMonodromy :=
  lie_mem_lieAlgebra_of_commutator_le (D.commutator_zeroLocus_le_zeroLocus_geometricMonodromy _)
    hX hY

/-- The derived algebra of `Lie G°` lies in `Lie H°`. Over an algebraically closed field of
characteristic zero the identity components have the same Lie algebras as `G` and `H`.
(blueprint: `sk-i-restriction`, `lem-ag-closure-commutators`) -/
theorem lie_mem_lieAlgebra_identityComponent_geometricMonodromy [IsAlgClosed k] [CharZero k]
    {X Y : Matrix n n k} (hX : X ∈ lieAlgebra (identityComponent D.arithmeticMonodromy))
    (hY : Y ∈ lieAlgebra (identityComponent D.arithmeticMonodromy)) :
    ⁅X, Y⁆ ∈ lieAlgebra (identityComponent D.geometricMonodromy) := by
  rw [lieAlgebra_identityComponent] at hX hY ⊢
  exact D.lie_mem_lieAlgebra_geometricMonodromy hX hY

end Lie

section Semisimple

/-- **Normal restriction.** A semisimple Weil representation is geometrically semisimple: the
restriction of a semisimple datum to the normal subgroup `P = ker deg` is semisimple, by
Clifford's theorem `Representation.isSemisimpleRepresentation_comp_subtype`.
(blueprint: `lem-mg-normal-restriction-semisimple`) -/
theorem isSemisimpleRepresentation_degreeZero (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation (D.asRepresentation.comp D.degreeZero.subtype) :=
  Representation.isSemisimpleRepresentation_comp_subtype _ _

/-- The lattices of subrepresentations of `ρ` and of the defining representation of its arithmetic
monodromy group `G(k)` agree: a subspace is `ρ(W)`-stable if and only if it is stable under the
closure `G` (`forall_mulVec_mem_iff_forall_mem_zeroLocus_vanishingIdeal`). -/
noncomputable def subrepresentationOrderIsoArithmeticMonodromy :
    Subrepresentation D.asRepresentation ≃o
      Subrepresentation
        ((toRepresentation n k).comp (zeroLocus D.arithmeticMonodromy k).subtype) :=
  Subrepresentation.orderIsoOfForallIff fun U ↦ by
    have h := forall_mulVec_mem_iff_forall_mem_zeroLocus_vanishingIdeal (Γ := D.rep.range)
      (U := U)
    simp only [asRepresentation_eq, MonoidHom.coe_comp, Function.comp_apply, toRepresentation_apply,
      Subgroup.coe_subtype, Subtype.forall]
    refine ⟨fun hU g hg v hv ↦ h.1 ?_ g hg v hv, fun hU w v hv ↦ hU _ ?_ v hv⟩
    · rintro _ ⟨w, rfl⟩ v hv
      exact hU w v hv
    · exact subset_zeroLocus_vanishingIdeal _ ⟨w, rfl⟩

/-- A semisimple datum is semisimple for its arithmetic monodromy group `G`: the defining
representation of `G(k)` on `n → k` is semisimple, because `ρ(W)` and `G` have the same stable
subspaces. (blueprint: `lem-ag-closure-semisimple`) -/
theorem isSemisimpleRepresentation_arithmeticMonodromy (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp (zeroLocus D.arithmeticMonodromy k).subtype) :=
  D.subrepresentationOrderIsoArithmeticMonodromy.complementedLattice_iff.1 hD

/-- A semisimple datum is semisimple for the identity component `G°` of its arithmetic monodromy
group: `G°` is normal in `G`, and Clifford's theorem applies.
(blueprint: `lem-ag-closure-semisimple`) -/
theorem isSemisimpleRepresentation_identityComponent_arithmeticMonodromy [IsAlgClosed k]
    (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp (zeroLocus (identityComponent D.arithmeticMonodromy) k).subtype)
      := by
  have hG₀ : zeroLocus (identityComponent D.arithmeticMonodromy) k ≤
      zeroLocus D.arithmeticMonodromy k :=
    zeroLocus_anti (le_identityComponent _)
  have := D.isSemisimpleRepresentation_arithmeticMonodromy hD
  have h := Representation.isSemisimpleRepresentation_comp_subtype
    ((toRepresentation n k).comp (zeroLocus D.arithmeticMonodromy k).subtype)
    ((zeroLocus (identityComponent D.arithmeticMonodromy) k).subgroupOf
      (zeroLocus D.arithmeticMonodromy k))
  refine (Subrepresentation.orderIsoOfForallIff fun U ↦ ?_).complementedLattice_iff.1 h
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subtype.forall,
    Subgroup.mem_subgroupOf, toRepresentation_apply]
  exact ⟨fun hU g hg v hv ↦ hU g (hG₀ hg) hg v hv, fun hU g _ hg v hv ↦ hU g hg v hv⟩

end Semisimple

section IsAlgClosed

/- The identity component `G°` is a closed subgroup scheme over an algebraically closed field
(`Matrix.GeneralLinearGroup.identityComponent`); this, and not the degree datum, is where the
hypothesis `IsAlgClosed k` below comes from. -/
variable [IsAlgClosed k]

/-- The number of connected components of the arithmetic monodromy group: the index of `G°(k)`
in `G(k)`. The hypothesis `IsAlgClosed k` comes from the `IsHopfIdeal` instance of the identity
component.
(blueprint: `sk-d-central`) -/
noncomputable def componentCount : ℕ :=
  ((zeroLocus (identityComponent D.arithmeticMonodromy) k).subgroupOf
    (zeroLocus D.arithmeticMonodromy k)).index

/-- An *admissible choice* consists of `m > 0` with a factorization `Fᵐ = c h`, `c ∈ Z(G°)°` and
`h ∈ H°`, together with a family of elements meeting every coset of `G°` in `G` exactly once,
indexed by the number `Fin D.componentCount` of those cosets. The hypothesis `IsAlgClosed k` comes
from the `IsHopfIdeal` instance of the identity component.
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
  /-- The factorization of `Fᵐ`. -/
  frobenius_pow_eq : D.frobenius ^ m = c * h
  /-- The coset representatives. -/
  g : Fin D.componentCount → GL n k
  /-- The representatives lie in `G`. -/
  g_mem : ∀ i, g i ∈ zeroLocus D.arithmeticMonodromy k
  /-- Every element of `G` lies in exactly one coset `g i · G°`. -/
  g_exists_unique : ∀ x ∈ zeroLocus D.arithmeticMonodromy k,
    ∃! i, (g i)⁻¹ * x ∈ zeroLocus (identityComponent D.arithmeticMonodromy) k

variable {D} in
/-- The degree `N = m r` of an admissible choice, where `r` is the number of connected components
of `G`.
(blueprint: `sk-d-central`) -/
noncomputable def AdmissibleChoice.degree (a : D.AdmissibleChoice) : ℕ := a.m * D.componentCount

variable {D} in
/-- The central element `z = ∏ gᵢ c gᵢ⁻¹` of an admissible choice, an ordered product over the
coset representatives.
(blueprint: `sk-d-central`) -/
noncomputable def AdmissibleChoice.centralElement (a : D.AdmissibleChoice) : GL n k :=
  (List.ofFn fun i ↦ a.g i * a.c * (a.g i)⁻¹).prod

variable [CharZero k]

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
group factors as `G° = Z(G°)° H°` on `k`-points. Over an algebraically closed field, with all three
groups reduced, this is equivalent to the scheme statement: `G°` is the image of the
multiplication map `Z(G°)° × H° → G°`.
(blueprint: `sk-p-product`) -/
theorem identityComponent_eq_center_mul_geometricMonodromy (hD : D.IsSemisimple) :
    (zeroLocus (identityComponent D.arithmeticMonodromy) k : Set (GL n k)) =
      zeroLocus (identityComponent (center (identityComponent D.arithmeticMonodromy))) k *
        zeroLocus (identityComponent D.geometricMonodromy) k := by
  sorry

end IsAlgClosed

end RepresentedDegreeDatum
