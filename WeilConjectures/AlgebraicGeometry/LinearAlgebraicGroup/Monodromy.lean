/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie
public import WeilConjectures.Mathlib.RepresentationTheory.Semisimple

/-!
# Degree data and their monodromy groups

A *degree datum* is a group `W` with a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one; its kernel is written `P`. It abstracts the Weil group of a variety over a
finite field with its degree map, and all declarations of this file live in the namespace
`AlgebraicGeometry.Monodromy`.  A *represented* degree datum adds a representation
`ρ : W → GL n k`, whose arithmetic and geometric monodromy groups are the Zariski closures
`G = closure ρ(W)` and `H = closure ρ(P)`, with `F = ρ(γ)`.  Nothing here involves a topology on
`W` or a sheaf: the whole setting is the degree datum.

The groups `G` and `H` are closed subgroup schemes of `GL_n`, given by their Hopf ideals
`Matrix.GeneralLinearGroup.vanishingIdeal` in
`Matrix.GeneralLinearGroup.CoordinateRing n k`.
Their groups of points, identity components, centers and Lie algebras are
`Matrix.GeneralLinearGroup.zeroLocus`, `identityComponent` and `center`.

This file collects the definitions and the propositions about monodromy groups that the weight
arguments rest on: that `H` is normal in `G` and absorbs commutators, the existence of a positive
central pair, and the central–geometric product `G° = Z(G°)° H°`. The normality and commutator
statements are instances of general facts about Zariski closures of subgroups of `GL n k`
(`Matrix.GeneralLinearGroup.zeroLocus_vanishingIdeal_le_normalizer` and
`Matrix.GeneralLinearGroup.commutator_zeroLocus_vanishingIdeal_le`). They make `H ⊆ G` a pair of
closed subgroup schemes of `GL_n` whose inclusion contains the commutators
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`); the Lie algebra statements and the
central–geometric product are the general results on such pairs in
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie`, applied to the
monodromy groups and read on `k`-points.

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `asRepresentation` and `IsSemisimple`.
* `RepresentedDegreeDatum.IsPositiveCentralPair`: positive central pairs `(N, z)`.
* `RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
  `RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`: normal restriction and passage
  to the closure.
* `RepresentedDegreeDatum.isSemisimpleRepresentation_standardRepresentation_identityComponent`:
  a semisimple datum acts semisimply through `G°`.
* `RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy`,
  `RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq`: the central–geometric
  product `G° = Z(G°)° H°`, as surjectivity of the multiplication morphism of group schemes and on
  `k`-points.
* `RepresentedDegreeDatum.exists_isPositiveCentralPair`: a positive central representative.

## Blueprint

`DegreeDatum`, `RepresentedDegreeDatum` and the attached definitions, among them
`RepresentedDegreeDatum.arithmeticMonodromy` and `RepresentedDegreeDatum.geometricMonodromy`,
implement `sk-d-monodromy`;
`RepresentedDegreeDatum.IsPositiveCentralPair` implements `sk-d-central`;
`RepresentedDegreeDatum.arithmeticMonodromy_le_geometricMonodromy`,
`RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
`RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
`RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
the instance
`containsCommutators_subgroupSchemeHom_arithmeticMonodromy_le_geometricMonodromy`,
`RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`,
`RepresentedDegreeDatum.lie_mem_lieAlgebra_identityComponent_geometricMonodromy` and
`RepresentedDegreeDatum.isSemisimpleRepresentation_standardRepresentation_identityComponent`
implement `sk-i-restriction`;
`RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy` and
`RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq` implement `sk-p-product`;
`RepresentedDegreeDatum.exists_isPositiveCentralPair` implements `sk-p-central`.
-/

@[expose] public section

open scoped Matrix Pointwise IsMulCommutative
open Matrix.GeneralLinearGroup AlgebraicGeometry.GeneralLinearGroup

namespace AlgebraicGeometry.Monodromy

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

/-- A datum is *semisimple* when `n → k` is a semisimple `W`-representation.  This is an `abbrev`
so that the underlying class `Representation.IsSemisimpleRepresentation` stays visible to
instance search.
(blueprint: `sk-d-monodromy`) -/
noncomputable abbrev IsSemisimple : Prop :=
  Representation.IsSemisimpleRepresentation D.asRepresentation

/-- A *positive central pair* for the datum is a pair `(N, z)` with `N > 0` and
`z ∈ Z(G) ∩ H Fᴺ`, where `H Fᴺ` is the right coset `H(k) · Fᴺ`, written as the pointwise product
of the set `H(k)` with the singleton `{Fᴺ}`.
(blueprint: `sk-d-central`) -/
def IsPositiveCentralPair (N : ℕ) (z : GL n k) : Prop :=
  0 < N ∧ z ∈ (zeroLocus (center D.arithmeticMonodromy) k : Set (GL n k)) ∩
    (zeroLocus D.geometricMonodromy k * {D.frobenius ^ N})

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
(blueprint: `sk-i-restriction`) -/
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
(blueprint: `sk-i-restriction`) -/
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

open AlgebraicGeometry CategoryTheory

universe u

/- The closed subgroup schemes `subgroupScheme I` of `𝔾𝕃(n; k)` require `n` and `k` in one universe,
so the scheme-theoretic statements about the monodromy groups do. -/
variable {W : Type*} [Group W] {n k : Type u} [Fintype n] [DecidableEq n] [Field k]
  (D : RepresentedDegreeDatum W n k)

/-- The geometric monodromy group contains the commutators of the arithmetic one, as closed
subgroup schemes of `GL_n`: this is `commutator_zeroLocus_le_zeroLocus_geometricMonodromy` on the
`R`-points for all `k`-algebras `R`, transported to the schemes. In particular `H` is a normal
subgroup scheme of `G` (`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`), and the
general results on such pairs of closed subgroups apply to `H ⊆ G`.
(blueprint: `sk-i-restriction`) -/
instance containsCommutators_subgroupSchemeHom_arithmeticMonodromy_le_geometricMonodromy :
    IsMonHom.ContainsCommutators (subgroupSchemeHom D.arithmeticMonodromy_le_geometricMonodromy) :=
  containsCommutators_subgroupSchemeHom _ (by
    intro R _ _
    exact D.commutator_zeroLocus_le_zeroLocus_geometricMonodromy R)

/-- The geometric monodromy group contains the derived subgroup `[G, G]` of the arithmetic one, as
closed subgroup schemes of `GL_n`: `J ≤ derivedIdeal I`. (blueprint: `sk-i-restriction`) -/
theorem geometricMonodromy_le_derivedIdeal_arithmeticMonodromy :
    D.geometricMonodromy ≤ derivedIdeal D.arithmeticMonodromy :=
  (containsCommutators_iff_le_derivedIdeal _).1 inferInstance

/-- The derived algebra of `Lie G` lies in `Lie H`, over any field, where `Lie H → Lie G` is the
differential `lieAlgebraMap` of the closed immersion `H ⟶ G`. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_lieAlgebra_geometricMonodromy
    (X Y : GrpObj.Lie (subgroupScheme D.arithmeticMonodromy)) :
    ∃ Z : GrpObj.Lie (subgroupScheme D.geometricMonodromy),
      lieAlgebraMap D.arithmeticMonodromy_le_geometricMonodromy Z = ⁅X, Y⁆ :=
  (LieHom.mem_range _ _).1 (lie_mem_range_lieAlgebraMap _ X Y)

/-- The derived algebra of `Lie G°` lies in `Lie H°`, over an algebraically closed field of
characteristic zero. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_lieAlgebra_identityComponent_geometricMonodromy [IsAlgClosed k] [CharZero k]
    (X Y : GrpObj.Lie (subgroupScheme (identityComponent D.arithmeticMonodromy))) :
    ∃ Z : GrpObj.Lie (subgroupScheme (identityComponent D.geometricMonodromy)),
      lieAlgebraMap (identityComponent_mono _ D.arithmeticMonodromy_le_geometricMonodromy) Z =
        ⁅X, Y⁆ :=
  (LieHom.mem_range _ _).1 (lie_mem_range_lieAlgebraMap_identityComponent _ X Y)

end Lie

section IsAlgClosed

/- The identity component `G°` is a closed subgroup scheme over an algebraically closed field
(`Matrix.GeneralLinearGroup.identityComponent`); this, and not the degree datum, is where the
hypothesis `IsAlgClosed k` comes from. The multiplication morphism `Z(G°)° × H° ⟶ G°` is a
morphism of group schemes over `Spec k`, so, as in the `Lie` section, `n` and `k` share a
universe. -/
universe u

variable {W : Type*} [Group W] {n k : Type u} [Fintype n] [DecidableEq n] [Field k]
  (D : RepresentedDegreeDatum W n k) [IsAlgClosed k] [CharZero k]

open CategoryTheory AlgebraicGeometry
open scoped MonObj

/-- A semisimple datum acts semisimply through the identity component of its arithmetic monodromy
group: the standard representation of `G°(k)` on `kⁿ` is semisimple.

Proof sketch (not formalised): `kⁿ` is a semisimple `W`-module, hence a semisimple module for the
Zariski closure `G(k)` of `ρ(W)`, since the stabilizer of a subspace is closed; `G°(k)` has finite
index in `G(k)`, so by Clifford's theorem (`Representation.isSemisimpleRepresentation_comp_subtype`)
`kⁿ` is a semisimple `G°(k)`-module. (blueprint: `sk-i-restriction`) -/
theorem isSemisimpleRepresentation_standardRepresentation_identityComponent
    (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation
      (standardRepresentation (identityComponent D.arithmeticMonodromy)) := by
  sorry

/-- For a semisimple represented degree datum the identity component of the arithmetic monodromy
group is the central–geometric product `G° = Z(G°)° H°`: the multiplication morphism
`Z(G°)° ×ₖ H° ⟶ G°` of group schemes is surjective. This is the general
`AlgebraicGeometry.GeneralLinearGroup.surjective_mulCenterIdentityComponent` for the pair
`H ⊆ G`, which contains the commutators of `G` and acts semisimply on `kⁿ`.
(blueprint: `sk-p-product`) -/
theorem surjective_mul_center_geometricMonodromy (hD : D.IsSemisimple) :
    Function.Surjective
      (mulCenterIdentityComponent D.arithmeticMonodromy_le_geometricMonodromy).left.base :=
  have := D.isSemisimpleRepresentation_standardRepresentation_identityComponent hD
  surjective_mulCenterIdentityComponent _

/-- The central–geometric product on `k`-points, in the form used to construct admissible choices:
every matrix of `G°(k)` is a product `c h` with `c ∈ Z(G°)°(k)` and `h ∈ H°(k)`. This is
`AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_containsCommutators` on the `k`-points,
read as matrices through `zeroLocusMulEquiv`; it supplies the factorization `Fᵐ = c h` of
`exists_isPositiveCentralPair`. (blueprint: `sk-p-product`) -/
theorem exists_mem_center_mul_mem_geometricMonodromy_eq (hD : D.IsSemisimple) {g : GL n k}
    (hg : g ∈ zeroLocus (identityComponent D.arithmeticMonodromy) k) :
    ∃ c ∈ zeroLocus (identityComponent (center (identityComponent D.arithmeticMonodromy))) k,
      ∃ h ∈ zeroLocus (identityComponent D.geometricMonodromy) k, c * h = g := by
  have := D.isSemisimpleRepresentation_standardRepresentation_identityComponent hD
  sorry

/-- The group theory behind `exists_isPositiveCentralPair`: let `H` be a subgroup of `Γ` containing
the commutators and `G₀` a subgroup of finite index such that every element of `G₀` is a product
`c h` with `c ∈ G₀` central in `G₀` and `h ∈ H`. Then for every `F` there are `N > 0` and a central
`z ∈ Γ` with `z ∈ H Fᴺ`. Pass to the normal core `K` of `G₀`, of index `e`: then `Fᵉ = c h`, and
`d = cᵉ` lies in the centre of `K`; the product `z` of the conjugates of `d` by representatives of
`Γ ⧸ K` is central, and it is congruent to `F^(e³)` modulo the commutators and `H`. -/
private theorem exists_pos_mem_center_mul_inv_mem {Γ : Type*} [Group Γ] (H G₀ : Subgroup Γ)
    (hH : commutator Γ ≤ H) [G₀.FiniteIndex] (F : Γ)
    (hfac : ∀ x ∈ G₀, ∃ c ∈ G₀, (∀ y ∈ G₀, c * y = y * c) ∧ ∃ h ∈ H, c * h = x) :
    ∃ N : ℕ, 0 < N ∧ ∃ z ∈ Subgroup.center Γ, z * (F ^ N)⁻¹ ∈ H := by
  classical
  set K := G₀.normalCore
  have : Finite (Γ ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  let : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  set e := Nat.card (Γ ⧸ K)
  have he : 0 < e := Nat.card_pos
  have hpow (x : Γ) : x ^ e ∈ K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨c, hcG₀, hc, h, hhH, hch⟩ := hfac _ (G₀.normalCore_le (hpow F))
  set d := c ^ e
  have hdK : d ∈ K := hpow c
  have hd (y : Γ) (hy : y ∈ K) : y * d = d * y :=
    ((Commute.pow_left (hc y (G₀.normalCore_le hy)) e)).symm
  let C : Subgroup Γ := Subgroup.centralizer (K : Set Γ) ⊓ K
  have : IsMulCommutative C := ⟨⟨fun a b ↦ Subtype.ext
    (Subgroup.mem_centralizer_iff.1 a.2.1 b b.2.2).symm⟩⟩
  have hconj (g : Γ) {x : Γ} (hx : x ∈ C) : g * x * g⁻¹ ∈ C := by
    refine ⟨Subgroup.mem_centralizer_iff.2 fun y hy ↦ ?_,
      Subgroup.Normal.conj_mem inferInstance x hx.2 g⟩
    have := Subgroup.mem_centralizer_iff.1 hx.1 (g⁻¹ * y * g)
      (Subgroup.Normal.conj_mem' inferInstance y hy g)
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  have hdC : d ∈ C := ⟨Subgroup.mem_centralizer_iff.2 fun y hy ↦ hd y hy, hdK⟩
  let f : Γ ⧸ K → C := fun q ↦ ⟨q.out * d * q.out⁻¹, hconj _ hdC⟩
  have hf (g : Γ) : (f (QuotientGroup.mk g) : Γ) = g * d * g⁻¹ := by
    obtain ⟨⟨y, hyK⟩, hy⟩ := QuotientGroup.mk_out_eq_mul K g
    change (QuotientGroup.mk g : Γ ⧸ K).out * d * (QuotientGroup.mk g : Γ ⧸ K).out⁻¹ = _
    rw [hy]
    calc g * y * d * (g * y)⁻¹ = g * (y * d) * y⁻¹ * g⁻¹ := by group
      _ = g * d * g⁻¹ := by rw [hd y hyK]; group
  let z : C := ∏ q, f q
  refine ⟨e * e * e, by positivity, z, Subgroup.mem_center_iff.2 fun g ↦ ?_, ?_⟩
  · let φ : C →* C := ((MulAut.conj g).toMonoidHom.comp C.subtype).codRestrict C
      fun x ↦ hconj g x.2
    have hφ : φ z = z := by
      rw [map_prod]
      refine Fintype.prod_equiv (MulAction.toPerm g) _ _ fun q ↦ Subtype.ext ?_
      induction q using QuotientGroup.induction_on with | H x => ?_
      change g * (f x : Γ) * g⁻¹ = (f (QuotientGroup.mk (g * x)) : Γ)
      rw [hf, hf]
      group
    have : g * (z : Γ) * g⁻¹ = z := congrArg Subtype.val hφ
    calc g * (z : Γ) = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [this]
  · let ψ : C →* Abelianization Γ := Abelianization.of.comp C.subtype
    have hψ : Abelianization.of (z : Γ) = Abelianization.of d ^ e := by
      change ψ z = _
      rw [map_prod]
      trans ∏ _q : Γ ⧸ K, Abelianization.of d
      · refine Finset.prod_congr rfl fun q _ ↦ ?_
        change Abelianization.of (q.out * d * q.out⁻¹) = _
        rw [map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      · rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hmem : z * (F ^ (e * e * e))⁻¹ * h ^ (e * e) ∈ commutator Γ := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψ, pow_mul,
        pow_mul, map_pow, map_pow, map_pow, ← hch, map_mul, mul_pow, map_pow, mul_pow, ← pow_mul,
        ← pow_mul]
      rw [mul_inv, mul_inv_cancel_left, inv_mul_cancel]
    simpa using H.mul_mem (hH hmem) (H.inv_mem (H.pow_mem hhH (e * e)))

/-- Every semisimple represented degree datum admits a positive central pair `(N, z)`.

Proof: the component group `G(k) ⧸ G°(k)` is finite
(`AlgebraicGeometry.GeneralLinearGroup.finiteIndex_subgroupOf_zeroLocus_identityComponent`), every
element of `G°(k)` is a product `c h` with `c` central in `G°(k)` and `h ∈ H(k)`
(`exists_mem_center_mul_mem_geometricMonodromy_eq`), and the commutators of `G(k)` lie in `H(k)`.
The group theory is then `exists_pos_mem_center_mul_inv_mem`: with `K` the normal core of `G°(k)`
in `G(k)`, of index `e`, factor `Fᵉ = c h`; then `cᵉ` is central in `K`, and the product of its
conjugates by representatives of `G(k) ⧸ K` is central in `G(k)` and lies in `H Fᴺ` for
`N = e³`.
(blueprint: `sk-p-central`) -/
theorem exists_isPositiveCentralPair (hD : D.IsSemisimple) :
    ∃ (N : ℕ) (z : GL n k), D.IsPositiveCentralPair N z := by
  have hG₀ : zeroLocus (identityComponent D.arithmeticMonodromy) k ≤
      zeroLocus D.arithmeticMonodromy k :=
    zeroLocus_anti (le_identityComponent _)
  have hH := D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k
  have := finiteIndex_subgroupOf_zeroLocus_identityComponent D.arithmeticMonodromy
  obtain ⟨N, hN, z, hz, hzF⟩ := exists_pos_mem_center_mul_inv_mem
    ((zeroLocus D.geometricMonodromy k).subgroupOf (zeroLocus D.arithmeticMonodromy k))
    ((zeroLocus (identityComponent D.arithmeticMonodromy) k).subgroupOf
      (zeroLocus D.arithmeticMonodromy k))
    (by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_subgroupOf]
      exact D.commutator_zeroLocus_le_zeroLocus_geometricMonodromy k
        (Subgroup.commutator_mem_commutator x.2 y.2))
    ⟨D.frobenius, D.rep_mem_zeroLocus_arithmeticMonodromy _⟩
    (by
      intro x hx
      obtain ⟨c, hc, h, hh, hch⟩ := D.exists_mem_center_mul_mem_geometricMonodromy_eq hD hx
      obtain ⟨hc₀, hcc⟩ := (mem_zeroLocus_center_iff _).1
        (zeroLocus_anti (le_identityComponent _) hc)
      refine ⟨⟨c, hG₀ hc₀⟩, hc₀, fun y hy ↦ Subtype.ext (hcc _ hy),
        ⟨h, hH (zeroLocus_anti (le_identityComponent _) hh)⟩,
        zeroLocus_anti (le_identityComponent _) hh, Subtype.ext hch⟩)
  refine ⟨N, z, hN, (mem_zeroLocus_center_iff _).2 ⟨z.2, fun g hg ↦ ?_⟩,
    Set.mem_mul.2 ⟨_, hzF, _, rfl, ?_⟩⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩).symm
  · simp

end IsAlgClosed

end RepresentedDegreeDatum

end AlgebraicGeometry.Monodromy
