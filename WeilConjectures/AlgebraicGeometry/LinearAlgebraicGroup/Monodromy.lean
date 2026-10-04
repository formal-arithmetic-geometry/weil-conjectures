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
* `RepresentedDegreeDatum.arithmeticExtension`: the arithmetic monodromy extension `H ⋊ ℤ`, as
  pairs `(g, m)` with `g ∈ H Fᵐ`.
* `RepresentedDegreeDatum.RegularHom`, `RepresentedDegreeDatum.RegularHom.arithmeticExtensionHom`:
  a regular homomorphism `G → GL_m` carrying `ρ` to `ρ'`, and the induced degree-preserving
  homomorphism of arithmetic monodromy extensions, dense on degree components and preserving
  centres.
* `RepresentedDegreeDatum.det`, `RepresentedDegreeDatum.determinantHom`: the determinant line and
  the determinant morphism of arithmetic monodromy.
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
`RepresentedDegreeDatum.arithmeticExtension` implements `def-wf-arithmetic-monodromy-extension`;
`RepresentedDegreeDatum.RegularHom.arithmeticExtensionHom` and its properties implement
`lem-mg-degree-component-functoriality`;
`RepresentedDegreeDatum.det` implements `def-mg-determinant-line`;
`RepresentedDegreeDatum.determinantHom` implements `lem-mg-determinant-monodromy-morphism`;
`RepresentedDegreeDatum.exists_admissibleChoice` and
`RepresentedDegreeDatum.isPositiveCentralPair_centralElement` implement `sk-p-central`;
`RepresentedDegreeDatum.identityComponent_eq_center_mul_geometricMonodromy` implements
`sk-p-product`.
-/

@[expose] public section

open scoped Matrix Pointwise
open Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

section Representation

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

end Representation

section Determinant

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]

variable (n) in
/-- The determinant `GL n R →* GL 1 R`, with `GL 1 R` realized as the invertible `1 × 1`
matrices `GL Unit R`. -/
noncomputable def detUnit (R : Type*) [CommRing R] : GL n R →* GL Unit R :=
  (Units.map (Matrix.scalar Unit : R →+* Matrix Unit Unit R).toMonoidHom).comp det

@[simp]
theorem detUnit_apply {R : Type*} [CommRing R] (g : GL n R) (i j : Unit) :
    (detUnit n R g : Matrix Unit Unit R) i j = (g : Matrix n n R).det := by
  simp [detUnit, Matrix.scalar_apply]

theorem map_detUnit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL n R) :
    map f (detUnit n R g) = detUnit n S (map f g) := by
  ext i j
  simp [RingHom.map_det]

/-- The determinant is regular: evaluation at `det g` is evaluation at `g` composed with the
algebra map `x ↦ det (x_ij)` of coordinate rings. -/
theorem evalAlgHom_comp_evalAlgHom_detUnit {R : Type*} [CommRing R] [Algebra k R]
    (g : GL n R) :
    (evalAlgHom g).comp (evalAlgHom (detUnit n _ (genericUnit n k))) =
      evalAlgHom (detUnit n R g) := by
  rw [← evalAlgHom_map, map_detUnit]
  congr 2
  exact (algHomMulEquiv n k R).apply_symm_apply g

end Determinant

end Matrix.GeneralLinearGroup

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

section ArithmeticExtension

theorem frobenius_mem_zeroLocus_arithmeticMonodromy :
    D.frobenius ∈ zeroLocus D.arithmeticMonodromy k :=
  D.rep_mem_zeroLocus_arithmeticMonodromy _

/-- Conjugation by the arithmetic monodromy group preserves the geometric one, on `k`-points. -/
theorem mul_mul_inv_mem_zeroLocus_geometricMonodromy {g h : GL n k}
    (hg : g ∈ zeroLocus D.arithmeticMonodromy k) (hh : h ∈ zeroLocus D.geometricMonodromy k) :
    g * h * g⁻¹ ∈ zeroLocus D.geometricMonodromy k :=
  Subgroup.mem_subgroupOf.1 ((D.normal_zeroLocus_geometricMonodromy k).conj_mem
    ⟨h, D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k hh⟩
      (Subgroup.mem_subgroupOf.2 hh) ⟨g, hg⟩)

/-- The arithmetic monodromy extension `G_arith(ρ) = ⨆ₘ H × {m}` of the datum, realized as the
group of pairs `(g, m)` in `GL n k × ℤ` with `g ∈ H Fᵐ`. The element `(h, m)` of the semidirect
product `H ⋊ ℤ`, with `ℤ` acting on `H` by conjugation by the Frobenius `F`, corresponds to the pair
`(h Fᵐ, m)`; the first projection is the map to matrices and the second projection is the degree
map, whose fibres are the degree components `G^[m]`. Retaining the degree `m` makes the matrix map
`(g, m) ↦ g` non-injective in general.
(blueprint: `def-wf-arithmetic-monodromy-extension`) -/
noncomputable def arithmeticExtension : Subgroup (GL n k × Multiplicative ℤ) where
  carrier := {p | p.1 * D.frobenius ^ (-Multiplicative.toAdd p.2) ∈
    zeroLocus D.geometricMonodromy k}
  one_mem' := by
    change (1 : GL n k) * D.frobenius ^ (-Multiplicative.toAdd (1 : Multiplicative ℤ)) ∈
      zeroLocus D.geometricMonodromy k
    rw [toAdd_one, neg_zero, zpow_zero, mul_one]
    exact one_mem _
  mul_mem' {p q} hp hq := by
    have hF := zpow_mem D.frobenius_mem_zeroLocus_arithmeticMonodromy (Multiplicative.toAdd p.2)
    have h := mul_mem (show p.1 * D.frobenius ^ (-Multiplicative.toAdd p.2) ∈
        zeroLocus D.geometricMonodromy k from hp)
      (D.mul_mul_inv_mem_zeroLocus_geometricMonodromy hF (show q.1 * D.frobenius ^
        (-Multiplicative.toAdd q.2) ∈ zeroLocus D.geometricMonodromy k from hq))
    change (p * q).1 * D.frobenius ^ (-Multiplicative.toAdd (p * q).2) ∈
      zeroLocus D.geometricMonodromy k
    convert h using 1
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul]
    group
  inv_mem' {p} hp := by
    have hF := zpow_mem D.frobenius_mem_zeroLocus_arithmeticMonodromy (-Multiplicative.toAdd p.2)
    have h := D.mul_mul_inv_mem_zeroLocus_geometricMonodromy hF
      (inv_mem (show p.1 * D.frobenius ^ (-Multiplicative.toAdd p.2) ∈
        zeroLocus D.geometricMonodromy k from hp))
    change p⁻¹.1 * D.frobenius ^ (-Multiplicative.toAdd p⁻¹.2) ∈ zeroLocus D.geometricMonodromy k
    convert h using 1
    simp only [Prod.fst_inv, Prod.snd_inv, toAdd_inv]
    group

theorem mem_arithmeticExtension {p : GL n k × Multiplicative ℤ} :
    p ∈ D.arithmeticExtension ↔
      p.1 * D.frobenius ^ (-Multiplicative.toAdd p.2) ∈ zeroLocus D.geometricMonodromy k :=
  Iff.rfl

/-- The matrix of an element of the arithmetic monodromy extension lies in `G`. -/
theorem fst_mem_zeroLocus_arithmeticMonodromy {p : GL n k × Multiplicative ℤ}
    (hp : p ∈ D.arithmeticExtension) : p.1 ∈ zeroLocus D.arithmeticMonodromy k := by
  have h := mul_mem (D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k hp)
    (zpow_mem D.frobenius_mem_zeroLocus_arithmeticMonodromy (Multiplicative.toAdd p.2))
  rwa [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at h

/-- The matrix of an element of the arithmetic monodromy extension, as a point of `G`. -/
noncomputable def arithmeticExtensionToZeroLocus :
    D.arithmeticExtension →* zeroLocus D.arithmeticMonodromy k where
  toFun x := ⟨x.1.1, D.fst_mem_zeroLocus_arithmeticMonodromy x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rep_zpow_degreeOneElement (j : ℤ) :
    D.rep (D.degreeOneElement ^ j) = D.frobenius ^ j :=
  map_zpow _ _ _

/-- Every element `w` of `W` gives the element `(ρ(w), deg w)` of the arithmetic monodromy
extension. -/
theorem rep_deg_mem_arithmeticExtension (w : W) :
    (D.rep w, D.deg w) ∈ D.arithmeticExtension := by
  rw [mem_arithmeticExtension, ← rep_zpow_degreeOneElement, ← map_mul]
  refine D.rep_mem_zeroLocus_geometricMonodromy ?_
  change D.deg _ = 1
  rw [map_mul, map_zpow, D.deg_degreeOneElement, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_neg,
    ofAdd_toAdd, mul_inv_cancel]

end ArithmeticExtension

section RegularHom

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A *regular homomorphism* from a represented degree datum `D` to a datum `D'` on `m → k` with
the same degree datum: a homomorphism `r : G(k) → GL m k` from the arithmetic monodromy group of
`D`, carrying `ρ(w)` to `ρ'(w)`, whose matrix entries are regular functions on `G`, as witnessed by
an algebra map `comap` of coordinate rings. The induced action of `G` on a Weil-stable subquotient
of `V`, on a tensor construction of such, or on the determinant line, is such a homomorphism. -/
structure RegularHom (D : RepresentedDegreeDatum W n k) (D' : RepresentedDegreeDatum W m k) where
  /-- The homomorphism on `k`-points. -/
  toMonoidHom : zeroLocus D.arithmeticMonodromy k →* GL m k
  /-- The algebra map of coordinate rings witnessing regularity. -/
  comap : CoordinateRing m k →ₐ[k] CoordinateRing n k
  /-- The matrix entries of `toMonoidHom g` are the functions `comap x_ij` evaluated at `g`. -/
  evalAlgHom_comp_comap :
    ∀ g : zeroLocus D.arithmeticMonodromy k,
      (evalAlgHom (g : GL n k)).comp comap = evalAlgHom (toMonoidHom g)
  /-- Both data have the same degree datum. -/
  toDegreeDatum_eq : D'.toDegreeDatum = D.toDegreeDatum
  /-- The homomorphism carries `ρ` to `ρ'`. -/
  map_rep : ∀ w, toMonoidHom ⟨D.rep w, D.rep_mem_zeroLocus_arithmeticMonodromy w⟩ = D'.rep w

namespace RegularHom

variable {D} {D' : RepresentedDegreeDatum W m k} (f : D.RegularHom D')

theorem degreeZero_eq (f : D.RegularHom D') : D'.degreeZero = D.degreeZero := by
  simp only [degreeZero, f.toDegreeDatum_eq]

theorem map_frobenius :
    f.toMonoidHom ⟨D.frobenius, D.frobenius_mem_zeroLocus_arithmeticMonodromy⟩ = D'.frobenius := by
  simp only [frobenius]
  rw [f.map_rep, f.toDegreeDatum_eq]

/-- A regular homomorphism maps the geometric monodromy group of `D` into that of `D'`: an
equation of `H'` pulls back along `comap` to a function vanishing on `ρ(P)`, hence on `H`. -/
theorem map_mem_zeroLocus_geometricMonodromy {h : GL n k}
    (hh : h ∈ zeroLocus D.geometricMonodromy k) :
    f.toMonoidHom ⟨h, D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k hh⟩ ∈
      zeroLocus D'.geometricMonodromy k := by
  intro b hb
  rw [← f.evalAlgHom_comp_comap, AlgHom.comp_apply]
  refine hh _ (mem_vanishingIdeal.2 ?_)
  rintro _ ⟨p, hp, rfl⟩
  rw [← AlgHom.comp_apply,
    f.evalAlgHom_comp_comap ⟨D.rep p, D.rep_mem_zeroLocus_arithmeticMonodromy p⟩, f.map_rep]
  exact mem_vanishingIdeal.1 hb _ ⟨p, f.degreeZero_eq ▸ hp, rfl⟩

theorem mem_arithmeticExtension_map (x : D.arithmeticExtension) :
    (f.toMonoidHom (D.arithmeticExtensionToZeroLocus x), x.1.2) ∈ D'.arithmeticExtension := by
  have hF : (⟨D.frobenius, D.frobenius_mem_zeroLocus_arithmeticMonodromy⟩ :
      zeroLocus D.arithmeticMonodromy k) ^ (-Multiplicative.toAdd x.1.2) =
        ⟨D.frobenius ^ (-Multiplicative.toAdd x.1.2),
          zpow_mem D.frobenius_mem_zeroLocus_arithmeticMonodromy _⟩ := rfl
  rw [mem_arithmeticExtension]
  dsimp only
  rw [← f.map_frobenius, ← map_zpow, ← map_mul, hF]
  exact f.map_mem_zeroLocus_geometricMonodromy x.2

/-- The homomorphism `Φ(g, m) = (r(g), m)` of arithmetic monodromy extensions induced by a regular
homomorphism `r`; in the semidirect product description it is `(h, m) ↦ (r(h), m)`.
(blueprint: `lem-mg-degree-component-functoriality`) -/
noncomputable def arithmeticExtensionHom : D.arithmeticExtension →* D'.arithmeticExtension :=
  MonoidHom.codRestrict
    ((f.toMonoidHom.comp D.arithmeticExtensionToZeroLocus).prod
      ((MonoidHom.snd _ _).comp D.arithmeticExtension.subtype))
    _ f.mem_arithmeticExtension_map

@[simp]
theorem coe_arithmeticExtensionHom_apply (x : D.arithmeticExtension) :
    (f.arithmeticExtensionHom x : GL m k × Multiplicative ℤ) =
      (f.toMonoidHom (D.arithmeticExtensionToZeroLocus x), x.1.2) :=
  rfl

/-- `Φ` preserves the degree. (blueprint: `lem-mg-degree-component-functoriality`) -/
theorem snd_arithmeticExtensionHom (x : D.arithmeticExtension) :
    (f.arithmeticExtensionHom x : GL m k × Multiplicative ℤ).2 = x.1.2 :=
  rfl

/-- Evaluation at `g Fᵐ` is evaluation at `g` composed with an algebra map. -/
private theorem exists_evalAlgHom_mul (c : GL m k) (a : CoordinateRing m k) :
    ∃ b : CoordinateRing m k, ∀ g : GL m k, evalAlgHom g b = evalAlgHom (g * c) a := by
  refine ⟨evalAlgHom (genericUnit m k * map (algebraMap k (CoordinateRing m k)) c) a,
    fun g ↦ ?_⟩
  rw [← AlgHom.comp_apply, ← evalAlgHom_map, map_mul]
  congr 3
  · exact (algHomMulEquiv m k k).apply_symm_apply g
  · ext i j
    simp

/-- **Density on degree components.** The image of every degree component `G^[j]` of `D` under
`Φ` is Zariski dense in the degree component `G'^[j]` of `D'`: an equation vanishing on the
matrices of `Φ(G^[j])` vanishes on the matrices of `G'^[j]`. Both contain `ρ'(P γʲ)`, and an
equation vanishing on `ρ'(P) F'ʲ` vanishes on `H' F'ʲ` after translating by `F'ʲ`.
(blueprint: `lem-mg-degree-component-functoriality`) -/
theorem evalAlgHom_eq_zero_of_forall_snd_eq (j : Multiplicative ℤ) (a : CoordinateRing m k)
    (ha : ∀ x : D.arithmeticExtension, x.1.2 = j →
      evalAlgHom (f.arithmeticExtensionHom x : GL m k × Multiplicative ℤ).1 a = 0)
    {y : GL m k × Multiplicative ℤ} (hy : y ∈ D'.arithmeticExtension) (hyj : y.2 = j) :
    evalAlgHom y.1 a = 0 := by
  obtain ⟨b, hb⟩ := exists_evalAlgHom_mul (D'.frobenius ^ Multiplicative.toAdd j) a
  have hbH : b ∈ D'.geometricMonodromy := by
    refine mem_vanishingIdeal.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    have hγ : D'.degreeOneElement = D.degreeOneElement := by rw [f.toDegreeDatum_eq]
    rw [hb, frobenius, hγ, ← map_zpow, ← map_mul]
    have hp' : p ∈ D.degreeZero := f.degreeZero_eq ▸ hp
    replace hp' : D.deg p = 1 := hp'
    have hw : D.deg (p * D.degreeOneElement ^ Multiplicative.toAdd j) = j := by
      rw [map_mul, hp', one_mul, map_zpow, D.deg_degreeOneElement, ← ofAdd_zsmul, smul_eq_mul,
        mul_one, ofAdd_toAdd]
    have := ha ⟨_, D.rep_deg_mem_arithmeticExtension (p * D.degreeOneElement ^
      Multiplicative.toAdd j)⟩ hw
    change evalAlgHom (f.toMonoidHom ⟨D.rep _, D.rep_mem_zeroLocus_arithmeticMonodromy _⟩) a = 0
      at this
    rwa [f.map_rep] at this
  have := hy b hbH
  rwa [hb, hyj, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at this

open Matrix in
/-- **Centrality.** `Φ` maps central elements to central elements: commuting with a fixed matrix
is a closed condition, so by density on degree components `Φ(z)` commutes with every element of
the arithmetic monodromy extension of `D'`. (blueprint: `lem-mg-degree-component-functoriality`) -/
theorem arithmeticExtensionHom_mem_center {z : D.arithmeticExtension}
    (hz : z ∈ Subgroup.center D.arithmeticExtension) :
    f.arithmeticExtensionHom z ∈ Subgroup.center D'.arithmeticExtension := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  set c := (f.arithmeticExtensionHom z : GL m k × Multiplicative ℤ).1
  have hcomm : y.1.1 * c = c * y.1.1 := by
    ext i j
    have := f.evalAlgHom_eq_zero_of_forall_snd_eq y.1.2 (commutatorEquation c i j)
      (fun x _ ↦ by
        have h := congr(((($(congrArg f.arithmeticExtensionHom (hz x)) :
          D'.arithmeticExtension) : GL m k × Multiplicative ℤ).1))
        simp only [map_mul, Subgroup.coe_mul, Prod.fst_mul] at h
        rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul, h, sub_self])
      y.2 rfl
    rw [evalAlgHom_commutatorEquation, sub_eq_zero] at this
    simpa using this
  refine Subtype.ext (Prod.ext ?_ (mul_comm _ _))
  exact hcomm

end RegularHom

/-- The determinant line `det ρ = ⋀ⁿ ρ` of the datum: the rank-one datum `w ↦ det ρ(w)`, on
`Unit → k`, with the same degree datum. (blueprint: `def-mg-determinant-line`) -/
noncomputable def det : RepresentedDegreeDatum W Unit k where
  toDegreeDatum := D.toDegreeDatum
  rep := (detUnit n k).comp D.rep

/-- The determinant `G(k) → GL 1 k` is a regular homomorphism from `D` to its determinant line. -/
noncomputable def detRegularHom : D.RegularHom D.det where
  toMonoidHom := (detUnit n k).comp (zeroLocus D.arithmeticMonodromy k).subtype
  comap := evalAlgHom (detUnit n _ (genericUnit n k))
  evalAlgHom_comp_comap g := evalAlgHom_comp_evalAlgHom_detUnit (g : GL n k)
  toDegreeDatum_eq := rfl
  map_rep _ := rfl

/-- **The determinant morphism of arithmetic monodromy.** The determinant induces the
degree-preserving homomorphism `Δ(h, m) = (det h, m)` from the arithmetic monodromy extension of
`ρ` to that of `det ρ`. Its image is Zariski dense in every degree component
(`RegularHom.evalAlgHom_eq_zero_of_forall_snd_eq`) and it maps central elements to central elements
(`RegularHom.arithmeticExtensionHom_mem_center`).
(blueprint: `lem-mg-determinant-monodromy-morphism`) -/
noncomputable def determinantHom : D.arithmeticExtension →* D.det.arithmeticExtension :=
  D.detRegularHom.arithmeticExtensionHom

theorem coe_determinantHom_apply (x : D.arithmeticExtension) :
    (D.determinantHom x : GL Unit k × Multiplicative ℤ) = (detUnit n k x.1.1, x.1.2) :=
  rfl

/-- The determinant morphism maps central elements to central elements.
(blueprint: `lem-mg-determinant-monodromy-morphism`) -/
theorem determinantHom_mem_center {z : D.arithmeticExtension}
    (hz : z ∈ Subgroup.center D.arithmeticExtension) :
    D.determinantHom z ∈ Subgroup.center D.det.arithmeticExtension :=
  D.detRegularHom.arithmeticExtensionHom_mem_center hz

end RegularHom

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
