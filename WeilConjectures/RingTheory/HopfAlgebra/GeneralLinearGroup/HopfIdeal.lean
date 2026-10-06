/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# Hopf ideals of the coordinate ring of `GL_n` and their zero loci

This file is the purely algebraic side of the theory of closed subgroups of `GL_n`: it concerns
Hopf ideals `I` of the Hopf algebra `k[x_ij, det⁻¹]` and matrix groups, and never mentions
schemes. The group scheme `V(I)` itself and the comparison of its points with the matrix groups
defined here are in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup`.

For a Hopf ideal `I` and a `k`-algebra `R`, the invertible matrices over `R` on which every
equation in `I` vanishes form a subgroup `zeroLocus I R` of `GL n R`. Conversely, an abstract
subgroup `Γ` of `GL n k` has a Zariski closure, cut out by the ideal `vanishingIdeal Γ` of all
equations vanishing on `Γ`; this ideal is a Hopf ideal. Over an algebraically closed field the
Nullstellensatz identifies the ideal of the `k`-points of `zeroLocus I` with the radical of `I`.
Finally, the identity component and the centre of `V(I)` are described by Hopf ideals of
`k[x_ij, det⁻¹]`.

## Main definitions

- `Matrix.GeneralLinearGroup.zeroLocus`: the subgroup of `GL n R` of matrices satisfying the
  equations of a Hopf ideal `I`.
- `Matrix.GeneralLinearGroup.vanishingIdeal`: the ideal of equations vanishing on a set of
  matrices; for a subgroup, the ideal of its Zariski closure.
- `Matrix.GeneralLinearGroup.toPrimeSpectrum`: the point of `Spec k[x_ij, det⁻¹]` given by a
  matrix in `GL n k`.
- `Matrix.GeneralLinearGroup.identityComponent`: the ideal of the reduced identity component
  `G°` of `V(I)`.
- `Matrix.GeneralLinearGroup.IsConnected`: `I` is the ideal of its own reduced identity component.
- `Matrix.GeneralLinearGroup.center`: the ideal of the reduced centre `Z(G)` of `V(I)`.

## Main results

- `Matrix.GeneralLinearGroup.instIsHopfIdealVanishingIdeal`: the ideal of a subgroup of `GL n k`
  is a Hopf ideal.
- `Matrix.GeneralLinearGroup.vanishingIdeal_zeroLocus_eq_radical`: the Nullstellensatz for
  `GL_n` over an algebraically closed field.
- `Matrix.GeneralLinearGroup.zeroLocus_vanishingIdeal_le_normalizer`,
  `Matrix.GeneralLinearGroup.commutator_zeroLocus_vanishingIdeal_le`: Zariski closure preserves
  normalizing and commutator inclusions between subgroups of `GL n k`.
- `Matrix.GeneralLinearGroup.mulVec_mem_of_mem_zeroLocus_vanishingIdeal`: a subspace of `k^n`
  stable under a subgroup is stable under its Zariski closure.
- `Matrix.GeneralLinearGroup.exists_evalAlgHom_eq_det_of_mk_eq`,
  `Matrix.GeneralLinearGroup.evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal`: the determinant on
  a subquotient is a polynomial function, and a polynomial function with finitely many values on a
  subgroup takes the same values on its Zariski closure.

## Blueprint

- `sk-d-geometry`: matrix algebraic groups as reduced closed subgroups of `GL(V)`, their identity
  component and centre.
- `sk-i-restriction`: the Zariski closure of a subgroup of `GL n k` is an algebraic group, and
  closure preserves normalizing and commutator inclusions.
- `sk-p-geometry`: the identity component is cut out by a Hopf ideal.
-/

@[expose] public section

open WithConv

namespace Matrix.GeneralLinearGroup

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
  {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation at `g` composed with the antipode is evaluation at `g⁻¹`. -/
theorem evalAlgHom_comp_antipodeAlgHom (g : GL n R) :
    (evalAlgHom g).comp (antipodeAlgHom n k) = evalAlgHom g⁻¹ := by
  have hg : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g :=
    (algHomMulEquiv n k R).apply_symm_apply g
  refine algHom_ext fun i j ↦ ?_
  rw [AlgHom.comp_apply, antipodeAlgHom_coord, evalAlgHom_coord]
  conv_rhs => rw [← hg, ← map_inv]
  rfl

/-- The identity matrix satisfies the equations of a Hopf ideal. -/
theorem evalAlgHom_eq_zero_of_mem_one (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (1 : GL n R) a = 0 := by
  have h := congr(($(evalAlgHom_one (n := n) (k := k) (R := R))).ofConv a)
  rw [ofConv_toConv] at h
  rw [h, AlgHom.convOne_apply, Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) ha,
    map_zero]

/-- The product of two matrices satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_mul (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g h : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) (hh : ∀ a ∈ I, evalAlgHom h a = 0)
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (g * h) a = 0 := by
  have h := congr(($(evalAlgHom_mul (k := k) g h)).ofConv a)
  rw [ofConv_toConv] at h
  rw [h]
  exact Ideal.IsHopfIdeal.convMul_apply_eq_zero hg hh ha

/-- The inverse of a matrix satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_inv (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) {a : CoordinateRing n k} (ha : a ∈ I) :
    evalAlgHom g⁻¹ a = 0 := by
  rw [← evalAlgHom_comp_antipodeAlgHom, AlgHom.comp_apply]
  exact hg _ (Ideal.IsHopfIdeal.antipode_mem (R := k) ha)

/-- The `R`-points of the closed subgroup scheme `V(I)` of `GL_n` cut out by a Hopf ideal `I`: the
invertible matrices over `R` on which every equation in `I` vanishes.
(blueprint: `sk-d-geometry`) -/
noncomputable def zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] (R : Type*)
    [CommRing R] [Algebra k R] : Subgroup (GL n R) where
  carrier := {g | ∀ a ∈ I, evalAlgHom g a = 0}
  one_mem' _ ha := evalAlgHom_eq_zero_of_mem_one I ha
  mul_mem' hg hh _ ha := evalAlgHom_eq_zero_of_mem_mul I hg hh ha
  inv_mem' hg _ ha := evalAlgHom_eq_zero_of_mem_inv I hg ha

@[simp]
theorem mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {g : GL n R} :
    g ∈ zeroLocus I R ↔ ∀ a ∈ I, evalAlgHom g a = 0 :=
  Iff.rfl

theorem zeroLocus_anti {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]
    (h : I ≤ J) : zeroLocus J R ≤ zeroLocus I R :=
  fun _ hg a ha ↦ hg a (h ha)

variable {S : Type*} [CommRing S] [Algebra k S]

/-- An algebra homomorphism `R → S` maps the `R`-points of `V(I)` to its `S`-points. -/
theorem map_mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    {g : GL n R} (hg : g ∈ zeroLocus I R) : map φ.toRingHom g ∈ zeroLocus I S := by
  intro a ha
  rw [evalAlgHom_map, AlgHom.comp_apply, hg a ha, map_zero]

/-- Along an injective algebra homomorphism `R → S`, a matrix over `R` is an `R`-point of `V(I)` if
and only if its image is an `S`-point. -/
theorem map_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {φ : R →ₐ[k] S}
    (hφ : Function.Injective φ) {g : GL n R} :
    map φ.toRingHom g ∈ zeroLocus I S ↔ g ∈ zeroLocus I R := by
  refine ⟨fun hg a ha ↦ hφ ?_, map_mem_zeroLocus φ⟩
  rw [map_zero, ← AlgHom.comp_apply, ← evalAlgHom_map]
  exact hg a ha

/-- The group homomorphism `V(I)(R) →* V(I)(S)` induced by an algebra homomorphism `R → S`. -/
noncomputable def zeroLocus.map (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    (φ : R →ₐ[k] S) : zeroLocus I R →* zeroLocus I S :=
  ((Matrix.GeneralLinearGroup.map φ.toRingHom).comp (zeroLocus I R).subtype).codRestrict _
    fun g ↦ map_mem_zeroLocus φ g.2

@[simp]
theorem zeroLocus.coe_map_apply {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    (g : zeroLocus I R) :
    (zeroLocus.map I φ g : GL n S) = Matrix.GeneralLinearGroup.map φ.toRingHom g :=
  rfl

/-- The ideal of equations vanishing on a set `S` of invertible matrices over `k`. For a subgroup
`S`, it cuts out the Zariski closure of `S`. (blueprint: `sk-i-restriction`) -/
noncomputable def vanishingIdeal (S : Set (GL n k)) : Ideal (CoordinateRing n k) :=
  ⨅ g ∈ S, RingHom.ker (evalAlgHom (k := k) g)

theorem mem_vanishingIdeal {S : Set (GL n k)} {a : CoordinateRing n k} :
    a ∈ vanishingIdeal S ↔ ∀ g ∈ S, evalAlgHom g a = 0 := by
  simp [vanishingIdeal, Submodule.mem_iInf]

theorem vanishingIdeal_anti {S T : Set (GL n k)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun g hg ↦ mem_vanishingIdeal.1 ha g (h hg)

theorem le_vanishingIdeal_zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    I ≤ vanishingIdeal (zeroLocus I k : Set (GL n k)) :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun _ hg ↦ hg _ ha

/-- The equation `(g * h)_ij - (h * g)_ij = 0` in the entries of `g`, for a fixed matrix `h`. -/
noncomputable def commutatorEquation (h : GL n k) (i j : n) : CoordinateRing n k :=
  ∑ l, (coord n k i l * algebraMap k _ ((h : Matrix n n k) l j) -
    algebraMap k _ ((h : Matrix n n k) i l) * coord n k l j)

@[simp]
theorem evalAlgHom_commutatorEquation (g h : GL n k) (i j : n) :
    evalAlgHom g (commutatorEquation h i j) =
      ((g : Matrix n n k) * h) i j - ((h : Matrix n n k) * g) i j := by
  simp [commutatorEquation, Matrix.mul_apply, Finset.sum_sub_distrib]

end CommRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

theorem isRadical_vanishingIdeal (S : Set (GL n k)) : (vanishingIdeal S).IsRadical := by
  rintro a ⟨m, hm⟩
  refine mem_vanishingIdeal.2 fun g hg ↦ IsNilpotent.eq_zero ⟨m, ?_⟩
  rw [← map_pow]
  exact mem_vanishingIdeal.1 hm g hg

/-- The Zariski closure of a subgroup of `GL n k` is a closed subgroup scheme: the ideal of
equations vanishing on the subgroup is a Hopf ideal. (blueprint: `sk-i-restriction`) -/
instance instIsHopfIdealVanishingIdeal (Γ : Subgroup (GL n k)) :
    (vanishingIdeal (Γ : Set (GL n k))).IsHopfIdeal k where
  counit_eq_zero a ha := mem_vanishingIdeal.1 ha 1 Γ.one_mem
  map_mkQ_comul_eq_zero a ha := sorry
  antipode_mem a ha := mem_vanishingIdeal.2 fun g hg ↦
    (DFunLike.congr_fun (evalAlgHom_comp_antipodeAlgHom g) a).trans
      (mem_vanishingIdeal.1 ha _ (Γ.inv_mem hg))

theorem subset_zeroLocus_vanishingIdeal (Γ : Subgroup (GL n k)) :
    Γ ≤ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k :=
  fun g hg _ ha ↦ mem_vanishingIdeal.1 ha g hg

/-- The `k`-points of the Zariski closure of a subgroup `Γ` lie in `Γ` as soon as `Γ` is cut out by
some set `J` of equations. -/
theorem zeroLocus_vanishingIdeal_le {Γ : Subgroup (GL n k)} (J : Set (CoordinateRing n k))
    (hΓ : ∀ g ∈ Γ, ∀ a ∈ J, evalAlgHom g a = 0)
    (hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) → g ∈ Γ) :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k ≤ Γ :=
  fun g hg ↦ hJ g fun a ha ↦ hg a (mem_vanishingIdeal.2 fun h hh ↦ hΓ h hh a ha)

/-- If a subgroup `Γ` of `GL n k` normalizes a subgroup `Δ`, then the Zariski closure of `Γ`
normalizes the Zariski closure of `Δ`, on `R`-points for every `k`-algebra `R`.

Proof sketch (not formalized): over a field, `Γ × Δ` is schematically dense in the product of the
closures: if `∑ aᵢ ⊗ bᵢ` vanishes on `Γ × Δ` with the `bᵢ` linearly independent modulo
`vanishingIdeal Δ`, then every `aᵢ` vanishes on `Γ`. Apply this to the pullback of an equation of
`Δ` along `(g, h) ↦ g h g⁻¹`. (blueprint: `sk-i-restriction`) -/
theorem zeroLocus_vanishingIdeal_le_normalizer {Γ Δ : Subgroup (GL n k)}
    (hΓ : Γ ≤ Subgroup.normalizer (Δ : Set (GL n k)))
    (R : Type*) [CommRing R] [Algebra k R] :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R ≤
      Subgroup.normalizer (zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R : Set (GL n R)) := by
  sorry

/-- If the commutators of a subgroup `Γ` of `GL n k` lie in a subgroup `Δ`, then the commutators of
the Zariski closure of `Γ` lie in the Zariski closure of `Δ`, on `R`-points for every `k`-algebra
`R`.

Proof sketch (not formalized): the schematic density of `Γ × Γ` in the product of two copies of the
closure of `Γ`, as in `zeroLocus_vanishingIdeal_le_normalizer`, applied to the pullback of an
equation of `Δ` along `(g, h) ↦ g h g⁻¹ h⁻¹`. (blueprint: `sk-i-restriction`) -/
theorem commutator_zeroLocus_vanishingIdeal_le {Γ Δ : Subgroup (GL n k)} (hΓ : ⁅Γ, Γ⁆ ≤ Δ)
    (R : Type*) [CommRing R] [Algebra k R] :
    ⁅zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R,
        zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R⁆ ≤
      zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R := by
  sorry

/-- The linear equation `φ(g u) = 0` in the entries of `g`, for a vector `u` and a linear form
`φ` on `n → k`. -/
noncomputable def linearFormEquation (φ : Module.Dual k (n → k)) (u : n → k) :
    CoordinateRing n k :=
  ∑ i, ∑ j, algebraMap k _ (φ (fun l ↦ if i = l then 1 else 0) * u j) * coord n k i j

@[simp]
theorem evalAlgHom_linearFormEquation (φ : Module.Dual k (n → k)) (u : n → k) (g : GL n k) :
    evalAlgHom g (linearFormEquation φ u) = φ ((g : Matrix n n k) *ᵥ u) := by
  rw [LinearMap.pi_apply_eq_sum_univ φ]
  simp only [linearFormEquation, map_sum, map_mul, AlgHom.commutes, evalAlgHom_coord,
    Matrix.mulVec, dotProduct, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- **Closed stabilizers and density.** A subspace `S ⊆ k^n` stable under a subgroup `Γ` of
`GL n k` is stable under its Zariski closure: the stabilizer of `S` is cut out by the linear
equations `φ(g x) = 0`, for `x ∈ S` and `φ` in the annihilator of `S`.
(blueprint: `lem-wf-stabilizer-density`, `sk-i-restriction`) -/
theorem mulVec_mem_of_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    {S : Submodule k (n → k)} (hΓ : ∀ g ∈ Γ, ∀ x ∈ S, (g : Matrix n n k) *ᵥ x ∈ S) {g : GL n k}
    (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) {x : n → k} (hx : x ∈ S) :
    (g : Matrix n n k) *ᵥ x ∈ S := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).1 fun φ hφ ↦ ?_
  rw [← evalAlgHom_linearFormEquation]
  refine hg _ (mem_vanishingIdeal.2 fun γ hγ ↦ ?_)
  rw [evalAlgHom_linearFormEquation]
  exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (hΓ γ hγ x hx)

/-- A subspace `U ⊆ k^n` is stable under a subgroup `Γ` of `GL n k` if and only if it is stable
under its Zariski closure. (blueprint: `lem-wf-stabilizer-density`) -/
theorem forall_mulVec_mem_iff_forall_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    {U : Submodule k (n → k)} :
    (∀ g ∈ Γ, ∀ u ∈ U, (g : Matrix n n k) *ᵥ u ∈ U) ↔
      ∀ g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k, ∀ u ∈ U,
        (g : Matrix n n k) *ᵥ u ∈ U :=
  ⟨fun hU _ hg _ hu ↦ mulVec_mem_of_mem_zeroLocus_vanishingIdeal hU hg hu,
    fun hU g hg ↦ hU g (subset_zeroLocus_vanishingIdeal Γ hg)⟩

/-- The determinant of the endomorphism induced on a subquotient `S ⧸ U` of `k^n` by a matrix
`g` stabilizing `U ≤ S` is a polynomial function of the entries of `g`: there is one `p` in the
coordinate ring of `GL_n` with `p(g) = det f` for every `g` and every endomorphism `f` of `S ⧸ U`
induced by `g`.  In a basis `(mk sⱼ)` of `S ⧸ U`, with coordinate forms extended to linear forms
`νᵢ` on `k^n`, the matrix of `f` is `(νᵢ(g sⱼ))ᵢⱼ`, whose entries are linear in `g`.
(blueprint: `sk-p-readout`) -/
theorem exists_evalAlgHom_eq_det_of_mk_eq (S U : Submodule k (n → k)) :
    ∃ p : CoordinateRing n k, ∀ (g : GL n k) (f : Module.End k (S ⧸ U.comap S.subtype)),
      (∀ x : S, ∃ y : S, (y : n → k) = (g : Matrix n n k) *ᵥ x ∧
        f (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) →
      evalAlgHom g p = LinearMap.det f := by
  classical
  let b := Module.finBasis k (S ⧸ U.comap S.subtype)
  choose s hs using fun j ↦ Submodule.Quotient.mk_surjective _ (b j)
  choose ν hν using fun i ↦ LinearMap.exists_extend ((b.coord i).comp (U.comap S.subtype).mkQ)
  refine ⟨(Matrix.of fun i j ↦ linearFormEquation (ν i) (s j : n → k)).det, fun g f hf ↦ ?_⟩
  rw [← LinearMap.det_toMatrix b, AlgHom.map_det]
  congr 1
  ext i j
  obtain ⟨y, hy, hfy⟩ := hf (s j)
  have := congr($(hν i) y)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
    Module.Basis.coord_apply] at this
  simp [LinearMap.toMatrix_apply, ← hs, hfy, ← this, hy]

/-- A polynomial function `p` on `GL_n` whose values on a subgroup `Γ` lie in a finite set `A`
has its values in `A` on the whole Zariski closure of `Γ`: the product `∏_{a ∈ A} (p - a)`
vanishes on `Γ`. (blueprint: `sk-p-readout`) -/
theorem evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    (p : CoordinateRing n k) {A : Set k} (hA : A.Finite) (hΓ : ∀ γ ∈ Γ, evalAlgHom γ p ∈ A)
    {g : GL n k} (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) :
    evalAlgHom g p ∈ A := by
  classical
  have h := hg (∏ a ∈ hA.toFinset, (p - algebraMap k _ a)) (mem_vanishingIdeal.2 fun γ hγ ↦ by
    simpa [Finset.prod_eq_zero_iff, sub_eq_zero] using hΓ γ hγ)
  simpa [Finset.prod_eq_zero_iff, sub_eq_zero] using h

/-- Over an algebraically closed field, every maximal ideal of the coordinate ring of `GL_n` is the
ideal of a point. -/
theorem exists_ker_evalAlgHom_eq [IsAlgClosed k] (m : Ideal (CoordinateRing n k)) [m.IsMaximal] :
    ∃ g : GL n k, RingHom.ker (evalAlgHom g) = m := by
  let : Field (CoordinateRing n k ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (CoordinateRing n k ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let φ : CoordinateRing n k →ₐ[k] k :=
    (IsAlgClosed.lift : (CoordinateRing n k ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)
  refine ⟨algHomMulEquiv n k k (toConv φ), ?_⟩
  have hφ : evalAlgHom (algHomMulEquiv n k k (toConv φ)) = φ :=
    congrArg ofConv ((algHomMulEquiv n k k).symm_apply_apply (toConv φ))
  rw [hφ]
  ext a
  simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The Nullstellensatz for `GL_n`: over an algebraically closed field, an element vanishing at
every point where the equations `J` vanish lies in the radical of `J`. -/
theorem vanishingIdeal_setOf_le_radical [IsAlgClosed k] (J : Ideal (CoordinateRing n k)) :
    vanishingIdeal {g : GL n k | ∀ a ∈ J, evalAlgHom g a = 0} ≤ J.radical := by
  have : IsJacobsonRing (CoordinateRing n k) := isJacobsonRing_of_finiteType (A := k)
  intro a ha
  rw [J.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hJm, hm⟩
  obtain ⟨g, rfl⟩ := exists_ker_evalAlgHom_eq m
  exact mem_vanishingIdeal.1 ha g fun b hb ↦ hJm hb

/-- The Nullstellensatz for closed subgroup schemes of `GL_n`: the ideal of the `k`-points of
`V(I)` is the radical of `I`. (blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_eq_radical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : vanishingIdeal (zeroLocus I k : Set (GL n k)) = I.radical :=
  le_antisymm (vanishingIdeal_setOf_le_radical I)
    ((isRadical_vanishingIdeal _).radical_le_iff.2 (le_vanishingIdeal_zeroLocus I))

/-- Over an algebraically closed field, a radical Hopf ideal is the ideal of its `k`-points.
(blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_le_of_isRadical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] (hI : I.IsRadical) : vanishingIdeal (zeroLocus I k : Set (GL n k)) ≤ I :=
  ((vanishingIdeal_zeroLocus_eq_radical I).trans hI.radical).le

/-- The point of `Spec k[x_ij, det⁻¹]` given by an invertible matrix `g`: the kernel of evaluation
at `g`. -/
noncomputable def toPrimeSpectrum (g : GL n k) : PrimeSpectrum (CoordinateRing n k) :=
  ⟨RingHom.ker (evalAlgHom (k := k) g), RingHom.ker_isPrime _⟩

theorem toPrimeSpectrum_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    {g : GL n k} :
    toPrimeSpectrum g ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ↔
      g ∈ zeroLocus I k :=
  Iff.rfl

theorem toPrimeSpectrum_injective :
    Function.Injective (toPrimeSpectrum : GL n k → PrimeSpectrum (CoordinateRing n k)) := by
  intro g h hgh
  ext i j
  have hmem : coord n k i j - algebraMap k _ ((g : Matrix n n k) i j) ∈
      (toPrimeSpectrum g).asIdeal := by
    simp [toPrimeSpectrum]
  rw [hgh] at hmem
  exact (sub_eq_zero.1 (by simpa [toPrimeSpectrum] using hmem)).symm

/-- The ideal of the reduced identity component `G°` of the closed subscheme `V(I)` of `GL_n`: the
functions vanishing on the connected component of `V(I)` containing the identity matrix.
(blueprint: `sk-d-geometry`) -/
noncomputable def identityComponent (I : Ideal (CoordinateRing n k)) :
    Ideal (CoordinateRing n k) :=
  PrimeSpectrum.vanishingIdeal
    (connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
      (toPrimeSpectrum 1))

theorem le_identityComponent (I : Ideal (CoordinateRing n k)) : I ≤ identityComponent I :=
  (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ I).1 (connectedComponentIn_subset _ _)

theorem isRadical_identityComponent (I : Ideal (CoordinateRing n k)) :
    (identityComponent I).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- The reduced identity component is monotone in the group: if `V(J) ⊆ V(I)` then
`V(J)° ⊆ V(I)°`. -/
theorem identityComponent_mono (I : Ideal (CoordinateRing n k)) {J : Ideal (CoordinateRing n k)}
    (h : I ≤ J) : identityComponent I ≤ identityComponent J :=
  PrimeSpectrum.vanishingIdeal_anti_mono
    (connectedComponentIn_mono _ (PrimeSpectrum.zeroLocus_anti_mono h))

/-- The closed subgroup `V(I)` of `GL_n` is connected (and reduced): `I` is the ideal of its own
reduced identity component. -/
def IsConnected (I : Ideal (CoordinateRing n k)) : Prop :=
  identityComponent I = I

theorem IsConnected.isRadical {I : Ideal (CoordinateRing n k)} (h : IsConnected I) :
    I.IsRadical :=
  h ▸ isRadical_identityComponent I

/-- The identity component of an algebraic group over an algebraically closed field is a closed
subgroup scheme. (blueprint: `sk-p-geometry`) -/
instance [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    (identityComponent I).IsHopfIdeal k :=
  sorry

theorem one_mem_zeroLocus_identityComponent [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : (1 : GL n k) ∈ zeroLocus (identityComponent I) k := by
  intro a ha
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (I : Set _) :=
    toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ (mem_connectedComponentIn h1)

/-- The ideal of the reduced centre `Z(G)` of the closed subgroup scheme `G = V(I)` of `GL_n`: the
Zariski closure of the matrices of `G(k)` commuting with all of `G(k)`.
(blueprint: `sk-d-geometry`) -/
noncomputable def center (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Ideal (CoordinateRing n k) :=
  vanishingIdeal ((zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
    Subgroup (GL n k)) : Set (GL n k))

instance (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] : (center I).IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

/-- The ideal of `G` is contained in the ideal of its centre: `Z(G) ⊆ G`. -/
theorem le_center (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] : I ≤ center I :=
  (le_vanishingIdeal_zeroLocus I).trans (vanishingIdeal_anti fun _ hg ↦ hg.1)

/-- The `k`-points of the centre of `G = V(I)` are the matrices of `G(k)` commuting with all of
`G(k)`. (blueprint: `sk-d-geometry`) -/
theorem mem_zeroLocus_center_iff (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n k} :
    g ∈ zeroLocus (center I) k ↔ g ∈ zeroLocus I k ∧ ∀ h ∈ zeroLocus I k, g * h = h * g := by
  let J : Set (CoordinateRing n k) :=
    I ∪ {c | ∃ h ∈ zeroLocus I k, ∃ i j, c = commutatorEquation h i j}
  have hΓ : ∀ g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
      Subgroup (GL n k)), ∀ a ∈ J, evalAlgHom g a = 0 := by
    rintro g ⟨hg, hc⟩ a (ha | ⟨h, hh, i, j, rfl⟩)
    · exact hg a ha
    · rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul,
        Subgroup.mem_centralizer_iff.1 hc h hh, sub_self]
  have hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) →
      g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
        Subgroup (GL n k)) := by
    refine fun g hg ↦ ⟨fun a ha ↦ hg a (Or.inl ha),
      Subgroup.mem_centralizer_iff.2 fun h hh ↦ ?_⟩
    ext i j
    have := hg _ (Or.inr ⟨h, hh, i, j, rfl⟩)
    rw [evalAlgHom_commutatorEquation, sub_eq_zero] at this
    simpa using this.symm
  constructor
  · intro hg
    obtain ⟨hg, hc⟩ := zeroLocus_vanishingIdeal_le J hΓ hJ hg
    exact ⟨hg, fun h hh ↦ (Subgroup.mem_centralizer_iff.1 hc h hh).symm⟩
  · rintro ⟨hg, hc⟩
    exact subset_zeroLocus_vanishingIdeal _
      ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh ↦ (hc h hh).symm⟩

end Field

end Matrix.GeneralLinearGroup
