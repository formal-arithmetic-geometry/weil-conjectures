/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Archimedean
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Product
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.IdentityComponent

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
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie` and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Product`, applied to
the monodromy groups and read on `k`-points.

## Main declarations

* `DegreeDatum`, `RepresentedDegreeDatum`: the setting, with `arithmeticMonodromy`,
  `geometricMonodromy`, `frobenius`, `asRepresentation` and `IsSemisimple`.
* `DegreeDatum.exists_ker_eq_and_eq_mul_zpow`: a nonzero degree map is a multiple of the degree map
  of a degree datum.
* `DegreeDatum.lift`, `DegreeDatum.continuous_lift`: a homomorphism on `P = ker deg` and an
  operator `T` compatible with conjugation by `γ` extend to `u γⁿ ↦ f(u) Tⁿ`, continuously; this
  is the Weil fundamental representation.
* `RepresentedDegreeDatum.IsGeometricallySemisimple`: `n → k` is semisimple for `P`.
* `RepresentedDegreeDatum.IsPositiveCentralPair`: positive central pairs `(N, z)`.
* `RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
  `RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
  `RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`: normal restriction and passage
  to the closure.
* `RepresentedDegreeDatum.isSemisimpleRepresentation_degreeZero`,
  `RepresentedDegreeDatum.isSemisimpleRepresentation_arithmeticMonodromy`: a semisimple datum is
  semisimple for `P` and for `G(k)`.
* `RepresentedDegreeDatum.isSemisimpleRepresentation_standardRepresentation_identityComponent`:
  a semisimple datum acts semisimply through `G°`.
* `RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy`,
  `RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq`: the central–geometric
  product `G° = Z(G°)° H°`, as surjectivity of the multiplication morphism of group schemes and on
  `k`-points.
* `RepresentedDegreeDatum.exists_isPositiveCentralPair`: a positive central representative.
* `RepresentedDegreeDatum.ArithmeticMonodromyExtension`,
  `RepresentedDegreeDatum.arithmeticMonodromyExtensionHom`: the `k`-points `H(k) ⋊ ℤ` of the
  arithmetic monodromy extension and its map `(h, m) ↦ h Fᵐ` to matrices.
* `RepresentedDegreeDatum.degreeComponent`: the degree components `G^[m] = H × {m}`, with
  `degreeComponent_mul_degreeComponent` and `inv_degreeComponent` (the grading) and
  `image_degreeComponent_eq_closure` (their matrix images are the closures of `ρ(deg⁻¹(m))`).
* `RepresentedDegreeDatum.frobeniusConjIso`: conjugation by `F` as an automorphism of the group
  scheme `H`.
* `RepresentedDegreeDatum.map`, `RepresentedDegreeDatum.IsPositiveCentralPair.map`: a positive
  central pair transported along a polynomial homomorphism `GL n k →* GL m k`, such as the
  exterior power (`Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_exteriorPower`).

## Blueprint

`DegreeDatum`, `RepresentedDegreeDatum` and the attached definitions, among them
`RepresentedDegreeDatum.arithmeticMonodromy` and `RepresentedDegreeDatum.geometricMonodromy`,
implement `d-monodromy`; `RepresentedDegreeDatum.geometricMonodromy` also implements
`def-wf-geometric-monodromy-group`;
`RepresentedDegreeDatum.IsPositiveCentralPair` implements `d-central`;
`RepresentedDegreeDatum.arithmeticMonodromy_le_geometricMonodromy`,
`RepresentedDegreeDatum.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy`,
`RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy`,
`RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy`,
the instance
`containsCommutators_subgroupSchemeHom_arithmeticMonodromy_le_geometricMonodromy`,
`RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy`,
`RepresentedDegreeDatum.lie_mem_lieAlgebra_identityComponent_geometricMonodromy` and
`RepresentedDegreeDatum.isSemisimpleRepresentation_standardRepresentation_identityComponent`
implement `sk-i-restriction`, the normality, commutator and Lie statements also
`lem-ag-closure-commutators`;
`RepresentedDegreeDatum.isSemisimpleRepresentation_degreeZero` implements
`lem-mg-normal-restriction-semisimple`;
`RepresentedDegreeDatum.isSemisimpleRepresentation_arithmeticMonodromy` implements
the `G` part of `lem-ag-closure-semisimple`;
`RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy` and
`RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq` implement `sk-p-product`;
`RepresentedDegreeDatum.exists_isPositiveCentralPair` implements `sk-p-central` and `p-central`,
`RepresentedDegreeDatum.exists_pos_mem_center_mem_degreeComponent` implements
`lem-mg-common-positive-central-element`;
`RepresentedDegreeDatum.frobeniusConj`, `RepresentedDegreeDatum.frobeniusAction`,
`RepresentedDegreeDatum.ArithmeticMonodromyExtension` and
`RepresentedDegreeDatum.arithmeticMonodromyExtensionHom` implement, on `k`-points,
`def-wf-arithmetic-monodromy-extension`; that it is a group whose degree map is surjective with
kernel `H × {0}` (`lem-wf-arith-extension-group`) is Mathlib's `SemidirectProduct` group structure
with `SemidirectProduct.rightHom_surjective` and `SemidirectProduct.range_inl_eq_ker_rightHom`.
The tuple `(ρ, H, G_arith(ρ), G^[m])` of a represented degree datum is its monodromy data
(`def-wf-monodromy-data`).
`DegreeDatum.lift`, `DegreeDatum.lift_apply_of_mem_ker`, `DegreeDatum.lift_degreeOneElement` and
`DegreeDatum.continuous_lift` implement `lem-wf-weil-fundamental-representation`;
`RepresentedDegreeDatum.IsGeometricallySemisimple` implements `def-wf-geometric-semisimplicity`;
`RepresentedDegreeDatum.frobeniusConjIso` and its companions implement
`lem-wf-conjugation-geometric-monodromy` (`RepresentedDegreeDatum.frobeniusConj` is its action on
`k`-points); `RepresentedDegreeDatum.degreeComponent` implements `def-wf-degree-components`;
`RepresentedDegreeDatum.image_degreeComponent_eq_closure` implements
`lem-wf-degree-component-image`; `RepresentedDegreeDatum.degreeComponent_mul_degreeComponent` and
`RepresentedDegreeDatum.inv_degreeComponent` implement `lem-wf-degree-components-grading`. The
closure `G` of a subgroup is a closed subgroup (`lem-wf-zariski-closure-subgroup`) by
`Matrix.GeneralLinearGroup.instIsHopfIdealVanishingIdeal`. The pointer remarks
`rem-ptr-wf-arithmetic-monodromy-extension-1` and `rem-ptr-wf-degree-components-2` refer to the
statements above of `lem-wf-arith-extension-group`, `lem-wf-degree-component-image` and
`lem-wf-degree-components-grading`.
-/

@[expose] public section

open scoped Matrix Pointwise IsMulCommutative
open Matrix.GeneralLinearGroup AlgebraicGeometry.GeneralLinearGroup

namespace AlgebraicGeometry.Monodromy

/-- A degree datum: a group `W`, a surjective homomorphism `deg : W → ℤ` and a chosen element
`γ` of degree one.
(blueprint: `d-monodromy`) -/
structure DegreeDatum (W : Type*) [Group W] where
  /-- The degree homomorphism. -/
  deg : W →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  surjective_deg : Function.Surjective deg
  /-- The chosen element of degree one. -/
  degreeOneElement : W
  /-- The chosen element has degree one. -/
  deg_degreeOneElement : deg degreeOneElement = Multiplicative.ofAdd 1

/-- A degree map `deg` that is not identically zero is a multiple of the degree map of a degree
datum `D₀` with the same kernel: the degrees are the multiples of some `a ≠ 0`, and dividing by `a`
gives a surjective degree map. Every element `γ` is then `u γ₀ ^ m`, for the degree-one element
`γ₀` of `D₀` and some `u` of degree zero, so that every determinant weight at `γ` is `m` times
the corresponding weight at `γ₀`. -/
theorem DegreeDatum.exists_ker_eq_and_eq_mul_zpow {W : Type*} [Group W]
    (deg : W →* Multiplicative ℤ) (hdeg : ∃ w, deg w ≠ 1) (γ : W) :
    ∃ D₀ : DegreeDatum W, deg.ker = D₀.deg.ker ∧
      ∃ u ∈ deg.ker, ∃ m : ℤ, γ = u * D₀.degreeOneElement ^ m := by
  obtain ⟨w₁, hw₁⟩ := hdeg
  let H : AddSubgroup ℤ :=
    { carrier := {x | ∃ w, Multiplicative.toAdd (deg w) = x}
      add_mem' := by
        rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
        exact ⟨w * w', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨w⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic H
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  have hdvd (w : W) : a ∣ Multiplicative.toAdd (deg w) := by
    have : Multiplicative.toAdd (deg w) ∈ H := ⟨w, rfl⟩
    rwa [ha, Int.mem_zmultiples_iff] at this
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, Multiplicative.toAdd (deg w₀) = a := by
    have : a ∈ H := ha ▸ AddSubgroup.mem_zmultiples a
    exact this
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw₁ (by simpa using hdvd w₁)
  let deg₀ : W →* Multiplicative ℤ :=
    { toFun w := Multiplicative.ofAdd (Multiplicative.toAdd (deg w) / a)
      map_one' := by simp
      map_mul' x y := by
        rw [map_mul, toAdd_mul, Int.add_ediv_of_dvd_left (hdvd x), ofAdd_add] }
  have hdeg₀ (w : W) : Multiplicative.toAdd (deg₀ w) = Multiplicative.toAdd (deg w) / a := rfl
  have hker : deg.ker = deg₀.ker := by
    ext w
    obtain ⟨q, hq⟩ := hdvd w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← toAdd_eq_zero, ← toAdd_eq_zero, hdeg₀, hq,
      Int.mul_ediv_cancel_left _ ha0, mul_eq_zero, or_iff_right ha0]
  have hw₀' : deg₀ w₀ = Multiplicative.ofAdd 1 :=
    Multiplicative.toAdd.injective (by rw [hdeg₀, hw₀, Int.ediv_self ha0, toAdd_ofAdd])
  have hsurj : Function.Surjective deg₀ := fun x ↦
    ⟨w₀ ^ Multiplicative.toAdd x, Multiplicative.toAdd.injective (by
      rw [map_zpow, toAdd_zpow, hw₀', toAdd_ofAdd, smul_eq_mul, mul_one])⟩
  let D₀ : DegreeDatum W := ⟨deg₀, hsurj, w₀, hw₀'⟩
  set m := Multiplicative.toAdd (deg₀ γ)
  have hγ : γ = γ * (w₀ ^ m)⁻¹ * w₀ ^ m := (inv_mul_cancel_right γ _).symm
  have hu : γ * (w₀ ^ m)⁻¹ ∈ deg.ker := by
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hw₀']
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_one, add_neg_cancel,
      toAdd_one]
  exact ⟨D₀, hker, _, hu, m, hγ⟩

namespace DegreeDatum

variable {W : Type*} [Group W] (D : DegreeDatum W)

/-- Every `w` is `u γ ^ deg w` with `u = w γ ^ (-deg w)` of degree zero. -/
theorem mul_inv_zpow_mem_ker (w : W) :
    w * (D.degreeOneElement ^ (D.deg w).toAdd)⁻¹ ∈ D.deg.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, D.deg_degreeOneElement, ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ofAdd_toAdd, mul_inv_cancel]

theorem zpow_mul_mul_inv_zpow_mem_ker {u : W} (hu : u ∈ D.deg.ker) (m : ℤ) :
    D.degreeOneElement ^ m * u * (D.degreeOneElement ^ m)⁻¹ ∈ D.deg.ker :=
  D.deg.normal_ker.conj_mem u hu _

section Lift

variable {M : Type*} [Group M] (f : D.deg.ker →* M) (T : M)
  (hT : ∀ u (hu : u ∈ D.deg.ker), T * f ⟨u, hu⟩ * T⁻¹ =
    f ⟨D.degreeOneElement * u * D.degreeOneElement⁻¹, D.deg.normal_ker.conj_mem u hu _⟩)

include hT in
/-- The relation `T f(u) T⁻¹ = f(γ u γ⁻¹)` iterates to `Tᵐ f(u) T⁻ᵐ = f(γᵐ u γ⁻ᵐ)`. -/
theorem zpow_mul_mul_inv_zpow_eq (m : ℤ) (u : W) (hu : u ∈ D.deg.ker) :
    T ^ m * f ⟨u, hu⟩ * (T ^ m)⁻¹ = f ⟨_, D.zpow_mul_mul_inv_zpow_mem_ker hu m⟩ := by
  induction m using Int.induction_on generalizing u with
  | zero => simp
  | succ m ih =>
    calc T ^ ((m : ℤ) + 1) * f ⟨u, hu⟩ * (T ^ ((m : ℤ) + 1))⁻¹
        = T * (T ^ (m : ℤ) * f ⟨u, hu⟩ * (T ^ (m : ℤ))⁻¹) * T⁻¹ := by group
      _ = f ⟨_, D.deg.normal_ker.conj_mem _ (D.zpow_mul_mul_inv_zpow_mem_ker hu m) _⟩ := by
        rw [ih, hT]
      _ = _ := congrArg f (Subtype.ext (by group))
  | pred m ih =>
    have hv := D.zpow_mul_mul_inv_zpow_mem_ker hu (-(m : ℤ) - 1)
    have e : f ⟨_, D.zpow_mul_mul_inv_zpow_mem_ker hu (-(m : ℤ))⟩ = T * f ⟨_, hv⟩ * T⁻¹ := by
      rw [hT]
      exact congrArg f (Subtype.ext (by group))
    calc T ^ (-(m : ℤ) - 1) * f ⟨u, hu⟩ * (T ^ (-(m : ℤ) - 1))⁻¹
        = T⁻¹ * (T ^ (-(m : ℤ)) * f ⟨u, hu⟩ * (T ^ (-(m : ℤ)))⁻¹) * T := by group
      _ = T⁻¹ * (T * f ⟨_, hv⟩ * T⁻¹) * T := by rw [ih, e]
      _ = _ := by group

/-- **The Weil fundamental representation.** A homomorphism `f : P → M` on the degree-zero
subgroup `P = ker deg`, together with an element `T : M` satisfying
`T f(u) T⁻¹ = f(γ u γ⁻¹)`, extends to the homomorphism `W → M`, `u γⁿ ↦ f(u) Tⁿ`; every `w` is
uniquely `u γⁿ`, with `n = deg w`. For the Weil group `W(X₀)` with a lift `s` of the Frobenius
(`AlgebraicGeometry.Monodromy.DegreeDatum.ofWeilGroup`), `P = π₁(X)`, `f = ρ_geom` and
`T = T_s`, this is the Weil fundamental representation `ρ(γ sⁿ) = ρ_geom(γ) T_sⁿ`; it restricts
to `f` (`lift_apply_of_mem_ker`), sends `γ` to `T` (`lift_degreeOneElement`) and is continuous
when `f` is and `P` is open (`continuous_lift`).
(blueprint: `lem-wf-weil-fundamental-representation`, the extension step of
`def-wf-fundamental-representation`) -/
def lift : W →* M where
  toFun w := f ⟨_, D.mul_inv_zpow_mem_ker w⟩ * T ^ (D.deg w).toAdd
  map_one' := by
    have : (⟨_, D.mul_inv_zpow_mem_ker 1⟩ : D.deg.ker) = 1 := Subtype.ext (by simp)
    rw [this, map_one, map_one, toAdd_one, zpow_zero, mul_one]
  map_mul' x y := by
    have hxy : (D.deg (x * y)).toAdd = (D.deg x).toAdd + (D.deg y).toAdd := by
      rw [map_mul, toAdd_mul]
    have hu : (⟨_, D.mul_inv_zpow_mem_ker (x * y)⟩ : D.deg.ker) =
        ⟨_, D.mul_inv_zpow_mem_ker x⟩ *
          ⟨_, D.zpow_mul_mul_inv_zpow_mem_ker (D.mul_inv_zpow_mem_ker y) (D.deg x).toAdd⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hxy]
      group
    rw [hu, map_mul, ← D.zpow_mul_mul_inv_zpow_eq f T hT _ _ (D.mul_inv_zpow_mem_ker y),
      show T ^ (D.deg (x * y)).toAdd = T ^ (D.deg x).toAdd * T ^ (D.deg y).toAdd by
        rw [hxy, zpow_add]]
    group

theorem lift_apply (w : W) :
    D.lift f T hT w = f ⟨_, D.mul_inv_zpow_mem_ker w⟩ * T ^ (D.deg w).toAdd :=
  rfl

/-- The extension `lift` restricts to `f` on the degree-zero subgroup.
(blueprint: `lem-wf-weil-fundamental-representation`) -/
theorem lift_apply_of_mem_ker {u : W} (hu : u ∈ D.deg.ker) : D.lift f T hT u = f ⟨u, hu⟩ := by
  rw [lift_apply]
  have h : (D.deg u).toAdd = 0 := by rw [MonoidHom.mem_ker.1 hu, toAdd_one]
  have : (⟨_, D.mul_inv_zpow_mem_ker u⟩ : D.deg.ker) = ⟨u, hu⟩ := Subtype.ext (by simp [h])
  rw [this, h, zpow_zero, mul_one]

@[simp]
theorem lift_comp_subtype : (D.lift f T hT).comp D.deg.ker.subtype = f :=
  MonoidHom.ext fun u ↦ D.lift_apply_of_mem_ker f T hT u.2

/-- The extension `lift` sends the degree-one element `γ` to `T`.
(blueprint: `lem-wf-weil-fundamental-representation`) -/
@[simp]
theorem lift_degreeOneElement : D.lift f T hT D.degreeOneElement = T := by
  have : (⟨_, D.mul_inv_zpow_mem_ker D.degreeOneElement⟩ : D.deg.ker) = 1 :=
    Subtype.ext (by simp [D.deg_degreeOneElement])
  rw [lift_apply, this, map_one, one_mul, D.deg_degreeOneElement, toAdd_ofAdd, zpow_one]

end Lift

end DegreeDatum

/-- A represented degree datum adds to a degree datum a representation `ρ : W → GL n k` on
`n → k`.
Its tuple `(ρ, H_geom, G_arith, G^[m])` (`rep`, `geometricMonodromy`, `arithmeticMonodromy`,
`degreeComponent`) is the monodromy data of `ρ`.
(blueprint: `d-monodromy`, `def-wf-monodromy-data`) -/
structure RepresentedDegreeDatum (W : Type*) [Group W] (n k : Type*) [Fintype n] [DecidableEq n]
    [Field k] extends DegreeDatum W where
  /-- The representation. -/
  rep : W →* GL n k

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable (D : RepresentedDegreeDatum W n k)

/-- The subgroup `P = ker deg` of degree-zero elements.
(blueprint: `d-monodromy`) -/
def degreeZero : Subgroup W := D.deg.ker

instance : D.degreeZero.Normal :=
  D.deg.normal_ker

/-- The arithmetic monodromy group `G = closure ρ(W)`, as a closed subgroup scheme of `GL_n`: the
Hopf ideal of equations vanishing on `ρ(W)`, which cuts out the reduced Zariski closure.
(blueprint: `d-monodromy`) -/
noncomputable def arithmeticMonodromy : Ideal (CoordinateRing n k) :=
  vanishingIdeal (D.rep.range : Set (GL n k))

/-- The geometric monodromy group `H = closure ρ(P)`, as a closed subgroup scheme of `GL_n`: the
Hopf ideal of equations vanishing on `ρ(P)`, which cuts out the reduced Zariski closure. For the
Weil group `W(X₀, s)` (`AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`, with the degree datum
`DegreeDatum.ofWeilGroup`) the subgroup `P` is the geometric fundamental group, and this is the
geometric monodromy group `H_geom` of a representation of the Weil group.
(blueprint: `d-monodromy`, `def-wf-geometric-monodromy-group`) -/
noncomputable def geometricMonodromy : Ideal (CoordinateRing n k) :=
  vanishingIdeal (D.degreeZero.map D.rep : Set (GL n k))

instance : D.arithmeticMonodromy.IsHopfIdeal k :=
  inferInstanceAs ((vanishingIdeal (D.rep.range : Set (GL n k))).IsHopfIdeal k)

instance : D.geometricMonodromy.IsHopfIdeal k :=
  inferInstanceAs ((vanishingIdeal (D.degreeZero.map D.rep : Set (GL n k))).IsHopfIdeal k)

/-- The image `ρ(W)` of the representation lies in the arithmetic monodromy group.
(blueprint: `d-monodromy`) -/
theorem range_rep_le_zeroLocus_arithmeticMonodromy :
    D.rep.range ≤ zeroLocus D.arithmeticMonodromy k :=
  subset_zeroLocus_vanishingIdeal D.rep.range

theorem rep_mem_zeroLocus_arithmeticMonodromy (w : W) :
    D.rep w ∈ zeroLocus D.arithmeticMonodromy k :=
  D.range_rep_le_zeroLocus_arithmeticMonodromy ⟨w, rfl⟩

/-- The Frobenius element `F = ρ(γ)`.
(blueprint: `d-monodromy`) -/
def frobenius : GL n k := D.rep D.degreeOneElement

/-- The representation of `W` on `n → k` underlying the datum.
(blueprint: `d-monodromy`) -/
noncomputable def asRepresentation : Representation k W (n → k) where
  toFun w := Matrix.toLinAlgEquiv' (D.rep w : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

theorem asRepresentation_eq : D.asRepresentation = (toRepresentation n k).comp D.rep :=
  rfl

/-- A datum is *semisimple* when `n → k` is a semisimple `W`-representation.  This is an `abbrev`
so that the underlying class `Representation.IsSemisimpleRepresentation` stays visible to
instance search.
(blueprint: `d-monodromy`) -/
noncomputable abbrev IsSemisimple : Prop :=
  Representation.IsSemisimpleRepresentation D.asRepresentation

/-- A *positive central pair* for the datum is a pair `(N, z)` with `N > 0` and
`z ∈ Z(G) ∩ H Fᴺ`, where `H Fᴺ` is the right coset `H(k) · Fᴺ`, written as the pointwise product
of the set `H(k)` with the singleton `{Fᴺ}`. Only `k`-points of `Z(G)` occur, so `Z(G)(k)` is
written as `centerPoints`, the matrices of `G(k)` commuting with all of `G(k)`; this makes sense
over any field `k`.
(blueprint: `d-central`) -/
def IsPositiveCentralPair (N : ℕ) (z : GL n k) : Prop :=
  0 < N ∧ z ∈ (centerPoints D.arithmeticMonodromy : Set (GL n k)) ∩
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

section Semisimple

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
subspaces. (blueprint: the `G` part of `lem-ag-closure-semisimple`; the `G°` part is
`isSemisimpleRepresentation_standardRepresentation_identityComponent`) -/
theorem isSemisimpleRepresentation_arithmeticMonodromy (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp (zeroLocus D.arithmeticMonodromy k).subtype) :=
  D.subrepresentationOrderIsoArithmeticMonodromy.complementedLattice_iff.1 hD

end Semisimple

variable {D} in
/-- The central element of a positive central pair lies in the arithmetic monodromy group. -/
theorem IsPositiveCentralPair.mem_zeroLocus_arithmeticMonodromy {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) : z ∈ zeroLocus D.arithmeticMonodromy k :=
  ((mem_centerPoints_iff _).1 hz.2.1).1

variable {D} in
/-- The central element of a positive central pair commutes with the image of `W`. -/
theorem IsPositiveCentralPair.commute {N : ℕ} {z : GL n k} (hz : D.IsPositiveCentralPair N z)
    (w : W) : z * D.rep w = D.rep w * z :=
  ((mem_centerPoints_iff _).1 hz.2.1).2 _ (D.rep_mem_zeroLocus_arithmeticMonodromy w)

/-- The `k`-points of the arithmetic monodromy group preserve every subrepresentation of the
defining representation: invariance under `ρ(W)` passes to its Zariski closure.
(blueprint: `sk-i-restriction`) -/
theorem mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy {g : GL n k}
    (hg : g ∈ zeroLocus D.arithmeticMonodromy k) (S : Subrepresentation D.asRepresentation)
    {x : n → k} (hx : x ∈ S) : (g : Matrix n n k) *ᵥ x ∈ S :=
  mulVec_mem_of_mem_zeroLocus_vanishingIdeal (Γ := D.rep.range) (S := S.toSubmodule)
    (by
      rintro _ ⟨w, rfl⟩ y hy
      simpa [asRepresentation] using S.apply_mem_toSubmodule w hy) hg hx

section ArithmeticMonodromyExtension

end ArithmeticMonodromyExtension

section Map

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The represented degree datum `r ∘ ρ` obtained from a homomorphism `r : GL n k →* GL m k`. -/
def map (r : GL n k →* GL m k) : RepresentedDegreeDatum W m k :=
  { D.toDegreeDatum with rep := r.comp D.rep }

variable {D} in
/-- A positive central pair `(N, z)` is transported to the positive central pair `(N, r z)` along a
homomorphism `r : GL n k →* GL m k` given by polynomials, such as an exterior power.
(blueprint: `sk-i-restriction`) -/
theorem IsPositiveCentralPair.map {N : ℕ} {z : GL n k} (hz : D.IsPositiveCentralPair N z)
    (r : GL n k →* GL m k) (φ : CoordinateRing m k →ₐ[k] CoordinateRing n k)
    (hφ : ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (r g)) :
    (D.map r).IsPositiveCentralPair N (r z) := by
  obtain ⟨hN, -, h, hh, _, rfl, hzh⟩ := id hz
  refine ⟨hN, (mem_centerPoints_iff _).2 ⟨?_, fun g hg ↦ ?_⟩, r h, ?_, _, rfl, ?_⟩
  · exact map_mem_zeroLocus_vanishingIdeal r φ hφ (Γ := D.rep.range)
      (Γ' := (r.comp D.rep).range) (by rintro _ ⟨w, rfl⟩; exact ⟨w, rfl⟩)
      (hz.mem_zeroLocus_arithmeticMonodromy)
  · refine commute_of_mem_zeroLocus_vanishingIdeal (Γ := (r.comp D.rep).range) ?_ hg
    rintro _ ⟨w, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul, hz.commute w]
  · exact map_mem_zeroLocus_vanishingIdeal r φ hφ (Γ := D.degreeZero.map D.rep)
      (Γ' := D.degreeZero.map (r.comp D.rep))
      (by rintro _ ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩) hh
  · rw [← hzh, map_mul, map_pow]
    rfl

end Map

section Lie

open AlgebraicGeometry CategoryTheory

universe u

/- The closed subgroup schemes `subgroupScheme I` of `𝔾𝕃(n; k)` require `n` and `k` in one universe,
so the scheme-theoretic statements about the monodromy groups do. -/
variable {W : Type*} [Group W] {n k : Type u} [Fintype n] [DecidableEq n] [Field k]
  (D : RepresentedDegreeDatum W n k)

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

omit [CharZero k] in
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
  set A := D.arithmeticMonodromy
  have := D.isSemisimpleRepresentation_arithmeticMonodromy hD
  have := normal_zeroLocus_identityComponent (I := A) (isRadical_vanishingIdeal _) k
  have hC := Representation.isSemisimpleRepresentation_comp_subtype
    ((toRepresentation n k).comp (zeroLocus A k).subtype)
    ((zeroLocus (identityComponent A) k).subgroupOf (zeroLocus A k))
  -- a point of `G°` acts on `kⁿ` through its matrix
  have hpt (g : points (subgroupScheme (identityComponent A)) k) (v : n → k) :
      standardRepresentation (identityComponent A) g v =
        (((zeroLocusMulEquiv (identityComponent A) k).symm g : GL n k) : Matrix n n k) *ᵥ v := by
    rw [standardRepresentation, RationalHom.representation_apply, RationalHom.points_apply,
      Matrix.toLin'_apply]
    congr 3
    conv_lhs => rw [← (zeroLocusMulEquiv (identityComponent A) k).apply_symm_apply g]
    exact homMulEquiv_zeroLocusMulEquiv_comp _
  refine (Subrepresentation.orderIsoOfForallIff fun U ↦ ⟨fun h g v hv ↦ ?_,
    fun h g v hv ↦ ?_⟩).complementedLattice_iff.1 hC
  · set g' := (zeroLocusMulEquiv (identityComponent A) k).symm g
    have hg' : (g' : GL n k) ∈ zeroLocus A k := zeroLocus_anti (le_identityComponent A) g'.2
    rw [hpt]
    exact h ⟨⟨g', hg'⟩, Subgroup.mem_subgroupOf.2 g'.2⟩ v hv
  · have hg := h (zeroLocusMulEquiv (identityComponent A) k
      ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩) v hv
    rw [hpt, MulEquiv.symm_apply_apply] at hg
    exact hg

omit [CharZero k] in
/-- The `k`-points of the identity component `G°` of the arithmetic monodromy group act
semisimply on `kⁿ`: this is `isSemisimpleRepresentation_standardRepresentation_identityComponent`
for the matrices of the points. (blueprint: `sk-i-restriction`) -/
theorem isSemisimpleRepresentation_zeroLocus_identityComponent (hD : D.IsSemisimple) :
    Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp
        (zeroLocus (identityComponent D.arithmeticMonodromy) k).subtype) :=
  (isSemisimpleRepresentation_standardRepresentation_iff _).1
    (D.isSemisimpleRepresentation_standardRepresentation_identityComponent hD)

/-- The central–geometric product on `k`-points, in the form used to construct admissible choices:
every matrix of `G°(k)` is a product `c h` with `c ∈ Z(G°)°(k)` and `h ∈ H°(k)`. This is
`AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_commutator_mem` for the pair `H ⊆ G`,
whose commutators lie in `H` (`commutator_zeroLocus_le_zeroLocus_geometricMonodromy`); it
supplies the factorization `Fᵐ = c h` of `exists_isPositiveCentralPair`.
(blueprint: `sk-p-product`) -/
theorem exists_mem_center_mul_mem_geometricMonodromy_eq (hD : D.IsSemisimple) {g : GL n k}
    (hg : g ∈ zeroLocus (identityComponent D.arithmeticMonodromy) k) :
    ∃ c ∈ zeroLocus (identityComponent (center (identityComponent D.arithmeticMonodromy))) k,
      ∃ h ∈ zeroLocus (identityComponent D.geometricMonodromy) k, c * h = g :=
  have := D.isSemisimpleRepresentation_zeroLocus_identityComponent hD
  exists_mul_eq_of_commutator_mem D.arithmeticMonodromy_le_geometricMonodromy
    (fun _ ha _ hb ↦ D.commutator_zeroLocus_le_zeroLocus_geometricMonodromy _
      (Subgroup.commutator_mem_commutator ha hb)) hg

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
(`Matrix.GeneralLinearGroup.finiteIndex_zeroLocus_identityComponent`), every
element of `G°(k)` is a product `c h` with `c` central in `G°(k)` and `h ∈ H(k)`
(`exists_mem_center_mul_mem_geometricMonodromy_eq`), and the commutators of `G(k)` lie in `H(k)`.
The group theory is then `exists_pos_mem_center_mul_inv_mem`: with `K` the normal core of `G°(k)`
in `G(k)`, of index `e`, factor `Fᵉ = c h`; then `cᵉ` is central in `K`, and the product of its
conjugates by representatives of `G(k) ⧸ K` is central in `G(k)` and lies in `H Fᴺ` for
`N = e³`.
(blueprint: `sk-p-central`, `p-central`) -/
theorem exists_isPositiveCentralPair (hD : D.IsSemisimple) :
    ∃ (N : ℕ) (z : GL n k), D.IsPositiveCentralPair N z := by
  have hG₀ : zeroLocus (identityComponent D.arithmeticMonodromy) k ≤
      zeroLocus D.arithmeticMonodromy k :=
    zeroLocus_anti (le_identityComponent _)
  have hH := D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k
  have := finiteIndex_zeroLocus_identityComponent D.arithmeticMonodromy
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
  refine ⟨N, z, hN, (mem_centerPoints_iff _).2 ⟨z.2, fun g hg ↦ ?_⟩,
    Set.mem_mul.2 ⟨_, hzF, _, rfl, ?_⟩⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩).symm
  · simp

end IsAlgClosed

end RepresentedDegreeDatum

end AlgebraicGeometry.Monodromy
