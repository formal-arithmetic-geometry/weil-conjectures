/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Archimedean
public import Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.ExteriorPower

/-!
# Determinant weights of a degree datum

A *real character* is a homomorphism `λ : k^× → (ℝ, +)`.  Composing it with the
determinant character `δ_V(w) = det ρ_V(w)` of a representation and normalising by the
dimension produces the *determinant weight* `dw_λ(V) = λ(δ_V(γ)) / dim V`, a real number
attached to any representation of a degree datum whose determinant is finite on the degree-zero
subgroup `P = ker deg`.  The weight does not depend on the choice of the degree-one element `γ`.

The propositions here are the arithmetic that the weight bookkeeping of the Weil conjectures
runs on.  The *readout* says that a positive central pair `(N, z)` computes the determinant
weight of a subquotient on which `z` acts by a scalar `c_Q`: `dw_λ(Q) = λ(c_Q) / N`.  The
*tensor* and *exterior* propositions say that the determinant weights of the simple constituents
of `V ⊗ E` and of `⋀^s V` are, respectively, sums `dw_λ(V_i) + dw_λ(E_j)` and `s`-fold subsums of
the rank-counted weight list of `V`.  None of the three needs `V` or `E` to be semisimple,
except the exterior statement, which does.

Subrepresentations are Mathlib's `Subrepresentation`, so a subquotient is
`Subrepresentation.subquotient S U` for `U < S`, and semisimplicity is the class
`Representation.IsSemisimpleRepresentation`.

The readout is stated for a subquotient of the defining representation of the datum.  A general
rational representation `r` of the arithmetic monodromy group `G` is meant to reduce to this
case, because `r(G)` is again a matrix group, hence the defining representation of another
represented degree datum; that reduction needs a transport of the positive central pair `(N, z)`
along `r`, which is not stated here.

## Main declarations

* `Representation.RealCharacter`: a homomorphism `k^× → (ℝ, +)`.
* `Representation.HasFiniteGeometricDet`, `Representation.detWeight`: the finiteness of the
  determinant character on `P`, and the determinant weight `dw_λ`.
* `Representation.detWeight_mul_of_mem_ker`: the determinant weight does not depend on the choice
  of the degree-one element.
* `Representation.weightMultiset`: the rank-counted weight multiset of a decomposition.
* `RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair`: the weight readout from a
  positive central pair.
* `Representation.exists_detWeight_eq_add_of_subquotient_tprod`: the weights of the constituents
  of a tensor product.
* `Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: the weights of the
  constituents of an exterior power, over an algebraically closed field of characteristic zero.
* `DegreeDatum.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: the same for a degree
  datum, where the proof happens.
* `RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair_of_basis`: the readout for any
  representation whose matrices in a basis are those of the datum.

## Blueprint

`Representation.RealCharacter`, `Representation.HasFiniteGeometricDet`,
`Representation.detWeight` and `Representation.detWeight_mul_of_mem_ker` implement `sk-d-weights`;
`RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair` implements `sk-p-readout`;
`Representation.exists_detWeight_eq_add_of_subquotient_tprod` implements `sk-p-tensor`;
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower` implements
`sk-p-exterior`.  It is only the forward direction for a semisimple `V`, so it does not implement
the node `prop-ag-det-weight-exterior`, which allows a non-semisimple `V` and also asserts the
converse.
-/

@[expose] public section

open scoped Matrix

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- A *real character* of the field `k` is a group homomorphism `λ : kˣ → (ℝ, +)` from the units
of `k` to the reals under addition, `λ(ab) = λ(a) + λ(b)`. The weights of this file are read off
through such a character, from the determinants of representations (`detWeight`); for
`k = ℚ̄_ℓ` the relevant one is `log |ι(·)|` for a field embedding `ι : k → ℂ`.
(blueprint: `sk-d-weights`) -/
abbrev RealCharacter (k : Type*) [Field k] := kˣ →* Multiplicative ℝ

/-- A representation has *finite geometric determinant* for a degree homomorphism `deg` when its
determinant character takes only finitely many values on the degree-zero subgroup `P = ker deg`.
(blueprint: `sk-d-weights`) -/
def HasFiniteGeometricDet (deg : W →* Multiplicative ℤ) (ρ : Representation k W V) : Prop :=
  (Set.range fun w : deg.ker ↦ ρ.detCharacter w).Finite

/-- The *determinant weight* of a representation with respect to a real character `χ` and
a degree-one element `γ` is `dw_χ(ρ) = χ(δ(γ)) / dim V`.
(blueprint: `sk-d-weights`) -/
noncomputable def detWeight (χ : RealCharacter k) (γ : W) (ρ : Representation k W V) : ℝ :=
  Multiplicative.toAdd (χ (ρ.detCharacter γ)) / Module.finrank k V

/-- The determinant weight does not depend on the chosen degree-one element: replacing `γ` by
`u γ` for a degree-zero element `u` leaves it unchanged, because the determinant character takes
finitely many values on the degree-zero subgroup and `ℝ` is torsion-free.
(blueprint: `sk-d-weights`) -/
theorem detWeight_mul_of_mem_ker {deg : W →* Multiplicative ℤ} (ρ : Representation k W V)
    (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealCharacter k) (γ : W) {u : W}
    (hu : u ∈ deg.ker) : ρ.detWeight χ (u * γ) = ρ.detWeight χ γ := by
  sorry

/-- The rank-counted weight multiset of a family of subrepresentations: the determinant weight of
`Vs j` occurs `dim Vs j` times. -/
noncomputable def weightMultiset {ι : Type*} [Fintype ι] {ρ : Representation k W V}
    (χ : RealCharacter k) (γ : W) (Vs : ι → Subrepresentation ρ) : Multiset ℝ :=
  ∑ j : ι, Multiset.replicate (Module.finrank k (Vs j).toSubmodule)
    ((Vs j).toRepresentation.detWeight χ γ)

/-- Finiteness of the geometric determinant only depends on the degree-zero subgroup. -/
theorem hasFiniteGeometricDet_congr {deg deg' : W →* Multiplicative ℤ} (h : deg.ker = deg'.ker)
    (ρ : Representation k W V) : ρ.HasFiniteGeometricDet deg ↔ ρ.HasFiniteGeometricDet deg' := by
  unfold HasFiniteGeometricDet
  rw [h]

/-- Finiteness of the geometric determinant only depends on the determinant character. -/
theorem hasFiniteGeometricDet_iff_of_detCharacter_eq {V' : Type*} [AddCommGroup V'] [Module k V']
    {deg : W →* Multiplicative ℤ} {ρ : Representation k W V} {σ : Representation k W V'}
    (h : σ.detCharacter = ρ.detCharacter) :
    σ.HasFiniteGeometricDet deg ↔ ρ.HasFiniteGeometricDet deg := by
  unfold HasFiniteGeometricDet
  rw [h]

/-- The determinant weight only depends on the determinant character and the dimension. -/
theorem detWeight_eq_of_detCharacter_eq {V' : Type*} [AddCommGroup V'] [Module k V']
    {ρ : Representation k W V} {σ : Representation k W V'} (h : σ.detCharacter = ρ.detCharacter)
    (hd : Module.finrank k V' = Module.finrank k V) (χ : RealCharacter k) (γ : W) :
    σ.detWeight χ γ = ρ.detWeight χ γ := by
  unfold detWeight
  rw [h, hd]

/-- The determinant weight is homogeneous in the chosen element: `dw(γ ^ m) = m dw(γ)`. -/
theorem detWeight_zpow (ρ : Representation k W V) (χ : RealCharacter k) (γ : W) (m : ℤ) :
    ρ.detWeight χ (γ ^ m) = m * ρ.detWeight χ γ := by
  unfold detWeight
  rw [map_zpow, map_zpow, toAdd_zpow, zsmul_eq_mul, mul_div_assoc]

/-- The determinant weight at `u γ ^ m`, for `u` of degree zero, is `m` times that at `γ`. -/
theorem detWeight_mul_zpow_of_mem_ker {deg : W →* Multiplicative ℤ} (ρ : Representation k W V)
    (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealCharacter k) (γ : W) {u : W}
    (hu : u ∈ deg.ker) (m : ℤ) : ρ.detWeight χ (u * γ ^ m) = m * ρ.detWeight χ γ := by
  rw [ρ.detWeight_mul_of_mem_ker hdet χ _ hu, detWeight_zpow]

/-- If every element has degree zero, the determinant weight of a representation with finite
geometric determinant vanishes. -/
theorem detWeight_eq_zero_of_forall_deg_eq_one {deg : W →* Multiplicative ℤ}
    (hdeg : ∀ w, deg w = 1) (ρ : Representation k W V) (hdet : ρ.HasFiniteGeometricDet deg)
    (χ : RealCharacter k) (γ : W) : ρ.detWeight χ γ = 0 := by
  have := ρ.detWeight_mul_of_mem_ker hdet χ 1 (u := γ) (hdeg γ)
  rw [mul_one] at this
  rw [this, detWeight, map_one, map_one, toAdd_one, zero_div]

end Representation

namespace AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Fix a real character `χ` and a positive central pair `(N, z)` for a represented degree
datum.  If a nonzero `W`-subquotient `Q = S / U` of the defining representation has finite
geometric determinant and `z` acts on `Q` as the scalar `c`, then `dw_χ(Q) = χ(c) / N`.  The
scalar hypothesis is automatic when `Q` is simple, by Schur's lemma.
(blueprint: `sk-p-readout`) -/
theorem detWeight_eq_of_isPositiveCentralPair (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) {U S : Subrepresentation D.asRepresentation} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) (c : kˣ)
    (hc : ∀ x ∈ S, Matrix.toLinAlgEquiv' (z : Matrix n n k) x - (c : k) • x ∈ U) :
    (S.subquotient U).detWeight χ D.degreeOneElement =
      Multiplicative.toAdd (χ c) / N := by
  sorry

section Basis

open Module Matrix.GeneralLinearGroup

variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}

/-- A representation `ρ` whose matrices in a basis `b` are those of the datum is equivalent, via
the coordinates `b.equivFun`, to the defining representation of the datum. -/
noncomputable def basisEquiv (D : RepresentedDegreeDatum W n k) (b : Basis n k V)
    (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k)) :
    ρ.Equiv D.asRepresentation :=
  .mk b.equivFun fun w ↦ LinearMap.ext fun x ↦ by
    simp [asRepresentation, ← hρ, LinearMap.toMatrix_mulVec_repr]

/-- The `k`-points of the arithmetic monodromy group preserve every subrepresentation of a
representation `ρ` whose matrices in a basis `b` are those of the datum.
(blueprint: `sk-i-restriction`) -/
theorem toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy (D : RepresentedDegreeDatum W n k)
    (b : Basis n k V) (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k))
    {g : GL n k}
    (hg : g ∈ zeroLocus D.arithmeticMonodromy k) (S : Subrepresentation ρ) {x : V}
    (hx : x ∈ S) : Matrix.toLin b b (g : Matrix n n k) x ∈ S := by
  let e := D.basisEquiv b hρ
  rw [Matrix.toLin_apply_eq_equivFun_symm]
  exact (Subrepresentation.mem_orderIsoMapComap_iff e S).1
    (D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hg _
      (Subrepresentation.apply_mem_orderIsoMapComap e S hx))

/-- The weight readout `dw_χ(Q) = χ(c) / N` for a subquotient `Q = S / U` of any representation
`ρ` whose matrices in a basis `b` are those of the datum.
(blueprint: `sk-p-readout`) -/
theorem detWeight_eq_of_isPositiveCentralPair_of_basis (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) (b : Basis n k V)
    (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k))
    {U S : Subrepresentation ρ} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) (c : kˣ)
    (hc : ∀ x ∈ S, Matrix.toLin b b (z : Matrix n n k) x - (c : k) • x ∈ U) :
    (S.subquotient U).detWeight χ D.degreeOneElement =
      Multiplicative.toAdd (χ c) / N := by
  let e := D.basisEquiv b hρ
  let O := Subrepresentation.orderIsoMapComap e
  have hchar := Subrepresentation.detCharacter_subquotient_orderIsoMapComap e S U
  have hdim := (Subrepresentation.subquotientEquiv e S U).toLinearEquiv.finrank_eq
  rw [← Representation.detWeight_eq_of_detCharacter_eq hchar hdim.symm]
  refine D.detWeight_eq_of_isPositiveCentralPair χ hz (O.lt_iff_lt.2 hUS)
    ((Representation.hasFiniteGeometricDet_iff_of_detCharacter_eq hchar).2 hdet) c
    fun y hy ↦ (Subrepresentation.mem_orderIsoMapComap_iff e U).2 ?_
  have := hc _ ((Subrepresentation.mem_orderIsoMapComap_iff e S).1 hy)
  change b.equivFun.symm (_ *ᵥ b.equivFun (b.equivFun.symm y)) - (c : k) • b.equivFun.symm y ∈ U
    at this
  change b.equivFun.symm _ ∈ U
  rw [LinearEquiv.apply_symm_apply] at this
  rw [map_sub, map_smul]
  exact this

end Basis

end AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- Let `V` and `E` be finite-dimensional representations of one and the same degree datum, and
let `Q` be a simple constituent of `V ⊗ E`, presented as a subquotient `S / U` for
subrepresentations `U < S` of `V ⊗ E`.  If `Q` and the two subquotients produced below have
finite geometric determinant, then `dw_χ(Q) = dw_χ(V_i) + dw_χ(E_j)` for a simple constituent
`V_i` of `V` and a simple constituent `E_j` of `E`; these are the simple quotients of chosen
composition series of `V` and `E`.  Neither `V`, nor `E`, nor `V ⊗ E` is assumed semisimple.
(blueprint: `sk-p-tensor`) -/
theorem exists_detWeight_eq_add_of_subquotient_tprod
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (rV : Representation k W V) (rE : Representation k W E)
    {U S : Subrepresentation (rV.tprod rE)} (hUS : U < S)
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet deg) :
    ∃ UV SV : Subrepresentation rV, ∃ UE SE : Subrepresentation rE,
      UV < SV ∧ UE < SE ∧
      IsIrreducible (SV.subquotient UV) ∧ IsIrreducible (SE.subquotient UE) ∧
      (SV.subquotient UV).HasFiniteGeometricDet deg ∧
      (SE.subquotient UE).HasFiniteGeometricDet deg ∧
      (S.subquotient U).detWeight χ γ =
        (SV.subquotient UV).detWeight χ γ + (SE.subquotient UE).detWeight χ γ := by
  sorry

/-- The rank-counted list of a family of values: `∑ⱼ replicate (d j) (f j)` is the multiset of the
values of `f` along the first projection of `Σ j, Fin (d j)`. -/
private theorem sum_replicate_eq_map_univ_sigma {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (f : ι → ℝ) :
    ∑ j, Multiset.replicate (d j) (f j) =
      (Finset.univ : Finset (Σ j, Fin (d j))).val.map fun a ↦ f a.1 := by
  have h : (Finset.univ : Finset (Σ j, Fin (d j))).val.map (fun a ↦ f a.1) =
      ∑ a : Σ j, Fin (d j), ({f a.1} : Multiset ℝ) := by
    rw [Finset.sum_eq_multiset_sum]
    conv_lhs => rw [← Multiset.sum_map_singleton
      (Multiset.map (fun a : Σ j, Fin (d j) ↦ f a.1) Finset.univ.val)]
    rw [Multiset.map_map]
    rfl
  rw [h, Fintype.sum_sigma]
  simp [Multiset.nsmul_singleton]

end Representation

namespace AlgebraicGeometry.Monodromy

open Module Matrix.GeneralLinearGroup Representation

universe u

/-- The exterior-power weight theorem for a degree datum `D₀`, that is, for a surjective degree
map and a chosen element of degree one.  Following the blueprint: a positive central pair `(N, z)`
for the datum of `V` acts on each simple summand `Vs j` by a scalar `c_j` with
`dw(Vs j) = χ(c_j) / N`; on `⋀^s V` it is diagonal with entries `∏_{i ∈ I} c_i`, and on the
simple constituent `Q` by one of these, so the readout gives `dw(Q) = ∑_{i ∈ I} χ(c_i) / N`.
(blueprint: `sk-p-exterior`) -/
theorem DegreeDatum.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Type*} [Group W] (D₀ : DegreeDatum W)
    (χ : RealCharacter k)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet D₀.deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    {U S : Subrepresentation (rV.exteriorPower s)} (hUS : U < S)
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet D₀.deg) :
    ∃ T : Multiset ℝ, T ≤ weightMultiset χ D₀.degreeOneElement Vs ∧ Multiset.card T = s ∧
      (S.subquotient U).detWeight χ D₀.degreeOneElement = T.sum := by
  classical
  -- A basis of `V` adapted to the decomposition, indexed by `ULift (Fin r)`: the positive central
  -- pair is constructed for index types in the universe of `k`.
  let d : ι → ℕ := fun j ↦ finrank k (Vs j).toSubmodule
  let bσ : Basis (Σ j, Fin (d j)) k V :=
    hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule
  let eσ : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) ≃ Σ j, Fin (d j) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  -- The exterior power of `GL` uses the decidable equality of the linear order.
  let : DecidableEq (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) :=
    fun a b ↦ LinearOrder.toDecidableEq a b
  let b : Basis (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k V := bσ.reindex eσ.symm
  let idx : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) → ι := fun i ↦ (eσ i).1
  have hb_mem (i) : b i ∈ (Vs (idx i)).toSubmodule := by
    rw [Basis.reindex_apply]
    exact hdirect.collectedBasis_mem _ _
  -- The represented degree datum of `V` in the basis `b`, and a positive central pair.
  let D : RepresentedDegreeDatum W (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k :=
    { D₀ with rep := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp rV.toHomUnits }
  have hρ (w : W) : LinearMap.toMatrix b b (rV w) = (D.rep w : Matrix _ _ k) := by
    ext i i'
    rw [LinearMap.toMatrix_apply]
    exact (LinearMap.toMatrixAlgEquiv_apply b (rV w) i i').symm
  have hss : D.IsSemisimple :=
    (Subrepresentation.orderIsoMapComap (D.basisEquiv b hρ)).complementedLattice_iff.1
      (isSemisimpleRepresentation_of_isInternal Vs hsimpleVs hdirect)
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hss
  -- The central element `Z` acting on `V`.
  let Z : V →ₗ[k] V := Matrix.toLin b b (z : Matrix _ _ k)
  have hZcomm (w : W) : Z ∘ₗ rV w = rV w ∘ₗ Z := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hρ,
      LinearMap.toMatrix_toLin, ← Units.val_mul, ← Units.val_mul, hz.commute w]
  have hZmem (T : Subrepresentation rV) {x : V} (hx : x ∈ T) : Z x ∈ T :=
    D.toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy b hρ
      hz.mem_zeroLocus_arithmeticMonodromy T hx
  -- `Z` acts on each `Vs j` by a nonzero scalar `cs j`, and `dw(Vs j) = χ(cs j) / N`.
  have hscalar (j : ι) : ∃ c : kˣ, (∀ x ∈ (Vs j).toSubmodule, Z x = (c : k) • x) ∧
      (Vs j).toRepresentation.detWeight χ D₀.degreeOneElement =
        Multiplicative.toAdd (χ c) / N := by
    have hirr : IsIrreducible ((Vs j).subquotient ⊥) :=
      (Subrepresentation.orderIsoMapComap
        (Subrepresentation.subquotientBotEquiv (Vs j))).isSimpleOrder_iff.2 (hsimpleVs j)
    obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr Z
      (fun w x ↦ LinearMap.congr_fun (hZcomm w) x) (fun x hx ↦ hZmem ⊥ hx) (fun x hx ↦ hZmem _ hx)
    have hc' (x) (hx : x ∈ (Vs j).toSubmodule) : Z x = c • x :=
      sub_eq_zero.1 ((Submodule.mem_bot k).1 (hc x hx))
    have hbot : ⊥ < Vs j := (Subrepresentation.isAtom_of_isIrreducible (hsimpleVs j)).bot_lt
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt hbot
      refine hx0 ((Submodule.mem_bot k).2 ?_)
      have h0 : Z x = 0 := by rw [hc' x hx, zero_smul]
      rw [Matrix.toLin_apply_eq_equivFun_symm, LinearEquiv.map_eq_zero_iff] at h0
      have := congrArg (fun y ↦ (z⁻¹).val *ᵥ y) h0
      simpa [Matrix.mulVec_mulVec] using this
    have hchar := Subrepresentation.detCharacter_subquotient_bot (Vs j)
    refine ⟨Units.mk0 c hc0, hc', ?_⟩
    rw [← detWeight_eq_of_detCharacter_eq hchar
      (Subrepresentation.subquotientBotEquiv (Vs j)).toLinearEquiv.finrank_eq]
    exact D.detWeight_eq_of_isPositiveCentralPair_of_basis χ hz b hρ hbot
      ((hasFiniteGeometricDet_iff_of_detCharacter_eq hchar).2 (hdetVs j)) _
      fun x hx ↦ by
        rw [Units.val_mk0, show Matrix.toLin b b (z : Matrix _ _ k) x = Z x from rfl, hc' x hx,
          sub_self]
        exact Submodule.zero_mem _
  choose cs hcs hdw using hscalar
  have hZb (i) : Z (b i) = ((cs (idx i) : kˣ) : k) • b i := hcs _ _ (hb_mem i)
  -- The exterior power: its datum, the transported central pair, and `⋀^s Z`.
  let B := b.exteriorPower s
  let r : GL (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k →* GL _ k :=
    Matrix.GeneralLinearGroup.exteriorPower s
  obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq_evalAlgHom_exteriorPower (k := k)
    (n := ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) s
  have hz' := hz.map r φ hφ
  have hρ' (w : W) : LinearMap.toMatrix B B (rV.exteriorPower s w) =
      ((D.map r).rep w : Matrix _ _ k) := by
    change LinearMap.toMatrix B B (exteriorPower.map s (rV w)) = _
    rw [LinearMap.toMatrix_exteriorPower_map, hρ]
    rfl
  have hZ' : exteriorPower.map s Z = Matrix.toLin B B (r z : Matrix _ _ k) := by
    apply (LinearMap.toMatrix B B).injective
    rw [LinearMap.toMatrix_exteriorPower_map, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]
    rfl
  have hZ'mem (T : Subrepresentation (rV.exteriorPower s)) {x} (hx : x ∈ T) :
      exteriorPower.map s Z x ∈ T := by
    rw [hZ']
    exact (D.map r).toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy B hρ'
      hz'.mem_zeroLocus_arithmeticMonodromy T hx
  -- Schur's lemma on `Q = S / U`, and the eigenvalue of `⋀^s Z`.
  obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hsimple
    (exteriorPower.map s Z) (fun w x ↦ by
      change exteriorPower.map s Z (exteriorPower.map s (rV w) x) =
        exteriorPower.map s (rV w) (exteriorPower.map s Z x)
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hZcomm, exteriorPower.map_comp,
        LinearMap.comp_apply])
    (fun x hx ↦ hZ'mem U hx) (fun x hx ↦ hZ'mem S hx)
  have hev : Module.End.HasEigenvalue (exteriorPower.map s Z) c :=
    Module.End.hasEigenvalue_of_subquotient _ hUS (fun x hx ↦ hZ'mem U hx)
      (fun x hx ↦ hZ'mem S hx) c hc
  obtain ⟨I, hI⟩ := exteriorPower.exists_eq_prod_of_hasEigenvalue_map b hZb hev
  -- The weight readout on `Q`.
  have hQ := (D.map r).detWeight_eq_of_isPositiveCentralPair_of_basis χ hz' B hρ' hUS hdet
    (∏ i ∈ I.1, cs (idx i)) fun x hx ↦ by
      rw [← hZ', Units.coe_prod, ← hI]
      exact hc x hx
  refine ⟨I.1.val.map fun i ↦
    (Vs (idx i)).toRepresentation.detWeight χ D₀.degreeOneElement, ?_, ?_, ?_⟩
  · rw [weightMultiset, sum_replicate_eq_map_univ_sigma]
    calc _ ≤ (Finset.univ : Finset (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))))).val.map
          fun i ↦ (Vs (idx i)).toRepresentation.detWeight χ D₀.degreeOneElement :=
          Multiset.map_le_map (Finset.val_le_iff.2 (Finset.subset_univ _))
      _ = _ := by
        rw [← Finset.map_univ_equiv eσ, Finset.map_val, Multiset.map_map]
        rfl
  · simp
  · rw [← Finset.sum_eq_multiset_sum]
    refine hQ.trans ?_
    simp only [hdw, map_prod, toAdd_prod, Finset.sum_div]

end AlgebraicGeometry.Monodromy

namespace Representation

open AlgebraicGeometry.Monodromy

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- Let `V` be a nonzero semisimple representation of a degree datum over an algebraically closed
field of characteristic zero, written as an internal direct sum of simple subrepresentations
`Vs j`, with rank-counted weight multiset `Representation.weightMultiset χ γ Vs`: the multiset in
which the determinant weight of `Vs j` occurs `dim Vs j` times.  If the summands `Vs j` and the
simple constituent `Q = S / U` of `⋀^s V` all have finite geometric determinant, then `dw_χ(Q)` is
the sum of a sub-multiset of the weight multiset of size `s`, that is, `a_{i₁} + ⋯ + a_{i_s}` for
indices `i₁ < ⋯ < i_s` in the rank-counted weight list.

The degree map need not be surjective and `γ` need not have degree one: the degrees are the
multiples of some `a`, dividing by `a` gives a degree datum, and every weight at `γ` is the same
multiple of the corresponding weight at a degree-one element.  If all degrees vanish, all the
weights vanish.
(blueprint: `sk-p-exterior`) -/
theorem exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    {U S : Subrepresentation (rV.exteriorPower s)} (hUS : U < S)
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet deg) :
    ∃ T : Multiset ℝ, T ≤ weightMultiset χ γ Vs ∧ Multiset.card T = s ∧
      (S.subquotient U).detWeight χ γ = T.sum := by
  classical
  by_cases htriv : ∀ w, deg w = 1
  · -- Every element has degree zero: all the weights vanish.
    have hV0 (j : ι) := detWeight_eq_zero_of_forall_deg_eq_one htriv _ (hdetVs j) χ γ
    have hW : weightMultiset χ γ Vs =
        Multiset.replicate (Multiset.card (weightMultiset χ γ Vs)) 0 :=
      Multiset.eq_replicate_of_mem fun x hx ↦ by
        obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hx
        rw [hV0] at hj
        exact Multiset.eq_of_mem_replicate hj
    have hcard : Multiset.card (weightMultiset χ γ Vs) = Module.finrank k V := by
      rw [weightMultiset, Multiset.card_sum]
      simp only [Multiset.card_replicate]
      rw [Module.finrank_eq_card_basis
        (hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule),
        Fintype.card_sigma]
      simp
    have hs : s ≤ Module.finrank k V := by
      obtain ⟨x, hxS, hxU⟩ := SetLike.exists_of_lt hUS
      have hx0 : x ≠ 0 := fun h ↦ hxU (h ▸ Submodule.zero_mem _)
      have hpos : 0 < Module.finrank k (⋀[k]^s V) :=
        Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx0⟩
      rw [exteriorPower.finrank_eq] at hpos
      by_contra! h
      rw [Nat.choose_eq_zero_of_lt h] at hpos
      exact hpos.false
    refine ⟨Multiset.replicate s 0, ?_, Multiset.card_replicate _ _, ?_⟩
    · rw [hW, Multiset.replicate_le_replicate, hcard]
      exact hs
    · rw [detWeight_eq_zero_of_forall_deg_eq_one htriv _ hdet χ γ, Multiset.sum_replicate,
        smul_zero]
  -- Otherwise the degrees are the multiples of some `a ≠ 0`; divide by `a` to get a degree datum.
  simp only [not_forall] at htriv
  obtain ⟨w₁, hw₁⟩ := htriv
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
  -- `γ = u w₀ ^ m` with `u` of degree zero, so every weight at `γ` is `m` times that at `w₀`.
  set m := Multiplicative.toAdd (deg₀ γ)
  have hγ : γ = γ * (w₀ ^ m)⁻¹ * w₀ ^ m := (inv_mul_cancel_right γ _).symm
  have hu : γ * (w₀ ^ m)⁻¹ ∈ deg.ker := by
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hw₀']
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_one, add_neg_cancel,
      toAdd_one]
  obtain ⟨T₀, hle, hcard, hsum⟩ := D₀.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower χ rV
    s Vs hsimpleVs (fun j ↦ (hasFiniteGeometricDet_congr hker _).1 (hdetVs j)) hdirect hUS hsimple
    ((hasFiniteGeometricDet_congr hker _).1 hdet)
  refine ⟨T₀.map fun x ↦ (m : ℝ) * x, ?_, by rw [Multiset.card_map, hcard], ?_⟩
  · have : weightMultiset χ γ Vs = (weightMultiset χ w₀ Vs).map fun x ↦ (m : ℝ) * x := by
      rw [weightMultiset, weightMultiset, ← Multiset.coe_mapAddMonoidHom, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, hγ,
        detWeight_mul_zpow_of_mem_ker _ (hdetVs j) χ w₀ hu]
    rw [this]
    exact Multiset.map_le_map hle
  · rw [hγ, detWeight_mul_zpow_of_mem_ker _ hdet χ w₀ hu, Multiset.sum_map_mul_left,
      Multiset.map_id']
    exact congrArg _ hsum

end Representation
