/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Monodromy

/-!
# Determinant weights of a degree datum

A *real weight character* is a homomorphism `λ : k^× → (ℝ, +)`.  Composing it with the
determinant character `δ_V(w) = det ρ_V(w)` of a representation and normalising by the
dimension produces the *determinant weight* `dw_λ(V) = λ(δ_V(γ)) / dim V`, a real number
attached to any representation of a degree datum whose determinant is finite on the degree-zero
subgroup `P = ker deg`.
The three propositions here are the arithmetic that the weight bookkeeping of the Weil conjectures
runs on.  The *readout* says that a positive central pair `(N, z)` computes the determinant
weight of a subquotient on which `z` acts by a scalar `c_Q`: `dw_λ(Q) = λ(c_Q) / N`.  The
*tensor* and *exterior* propositions say that the determinant weights of the simple constituents of
`V ⊗ E` and of `⋀^s V` are, respectively, sums `dw_λ(V_i) + dw_λ(E_j)` and `s`-fold subsums of
the rank-counted weight list of `V`.  None of the three needs `V` or `E` to be semisimple,
except the exterior statement, which does.

## Main declarations

* `RealWeightCharacter`: a homomorphism `k^× → (ℝ, +)`.
* `Representation.detCharacter`, `Representation.HasFiniteGeometricDet`,
  `Representation.detWeight`: the determinant character, its finiteness on `P`, and the
  determinant weight `dw_λ`.
* `Representation.subquotient`, `Representation.ofInvariant`, `Representation.exteriorPower`: the
  auxiliary representations on a subquotient, on an invariant submodule, and on an exterior power.
* `RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair`: the weight readout from a
  positive central pair.
* `Representation.exists_detWeight_eq_add_of_subquotient_tprod`: the weights of the constituents of
  a tensor product.
* `Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: the weights of the
  constituents of an exterior power.
-/

@[expose] public section

open scoped Matrix Matrix.Zariski

/-- Blueprint `sk-d-weights`: Operations and weight characters.  A *real weight character* is a
group homomorphism `λ` from the units of `k` to the reals under addition. -/
abbrev RealWeightCharacter (k : Type*) [Field k] := kˣ →* Multiplicative ℝ

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Blueprint `sk-d-weights`: Operations and weight characters.  The *determinant character* of a
representation `ρ` is the homomorphism `δ(w) = det ρ(w)`, valued in the units of `k` because
`ρ(w)` is invertible. -/
noncomputable def detCharacter (ρ : Representation k W V) : W →* kˣ :=
  (Units.map (LinearMap.det : Module.End k V →* k)).comp (MonoidHom.toHomUnits ρ)

/-- Blueprint `sk-d-weights`: Operations and weight characters.  A representation has *finite
geometric determinant* for a degree homomorphism `deg` when its determinant character takes only
finitely many values on the degree-zero subgroup `P = ker deg`. -/
def HasFiniteGeometricDet (deg : W →* Multiplicative ℤ) (ρ : Representation k W V) : Prop :=
  (Set.range fun w : deg.ker ↦ ρ.detCharacter w).Finite

/-- Blueprint `sk-d-weights`: Operations and weight characters.  The *determinant weight* of a
representation with respect to a real weight character `λ` and a degree-one element `γ` is
`dw_λ(ρ) = λ(δ(γ)) / dim V`. -/
noncomputable def detWeight (lam : RealWeightCharacter k) (gamma : W) (ρ : Representation k W V) :
    ℝ :=
  Multiplicative.toAdd (lam (ρ.detCharacter gamma)) / Module.finrank k V

/-- The representation induced on the subquotient `S / U`, for `ρ`-invariant submodules `U ≤ S`
of `V`; here `U` is presented inside `S` as `U.comap S.subtype`, so no inclusion `U ≤ S` is
needed in the statement. -/
noncomputable def subquotient (ρ : Representation k W V) {U S : Submodule k V}
    (hU : ∀ w : W, ∀ x ∈ U, ρ w x ∈ U) (hS : ∀ w : W, ∀ x ∈ S, ρ w x ∈ S) :
    Representation k W (S ⧸ U.comap S.subtype) where
  toFun w := Submodule.mapQ _ _ ((ρ w).restrict (hS w)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    simpa only [LinearMap.coe_restrict_apply] using hU w x hx)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_one]
    exact congrArg _ (Subtype.ext (by simp))
  map_mul' v w := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul]
    exact congrArg _ (Subtype.ext (by simp))

/-- The zero submodule is invariant under every representation. -/
theorem bot_invariant (ρ : Representation k W V) :
    ∀ w : W, ∀ x ∈ (⊥ : Submodule k V), ρ w x ∈ (⊥ : Submodule k V) := by
  intro w x hx
  rw [Submodule.mem_bot] at hx ⊢
  simp [hx]

/-- The representation induced on a `ρ`-invariant submodule `S`, presented as the subquotient
`S / 0` so that it shares the API of `Representation.subquotient`. -/
noncomputable def ofInvariant (ρ : Representation k W V) {S : Submodule k V}
    (hS : ∀ w : W, ∀ x ∈ S, ρ w x ∈ S) :
    Representation k W (S ⧸ (⊥ : Submodule k V).comap S.subtype) :=
  ρ.subquotient ρ.bot_invariant hS

/-- The representation induced on the `s`-th exterior power `⋀^s V`, by functoriality of the
exterior power. -/
noncomputable def exteriorPower (ρ : Representation k W V) (s : ℕ) :
    Representation k W ↥(⋀[k]^s V) where
  toFun w := _root_.exteriorPower.map s (ρ w)
  map_one' := by
    rw [map_one]
    exact _root_.exteriorPower.map_id
  map_mul' v w := by
    rw [map_mul]
    exact _root_.exteriorPower.map_comp (ρ w) (ρ v)

end Representation

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Blueprint `sk-p-readout`: Central scalars and weight readout.  Fix a real weight character `λ`
and a positive central pair `(N, z)` for a represented degree datum.  If a nonzero `W`-subquotient
`Q = S / U` of the defining representation has finite geometric determinant and `z` acts on `Q` as
the scalar `c`, then `dw_λ(Q) = λ(c) / N`.  The scalar hypothesis is automatic when `Q` is simple,
by Schur's lemma; and the case of a general rational representation of the arithmetic monodromy
group `G` reduces to this one, because a rational representation of a matrix group is again a
matrix group representation, hence the defining representation of another represented degree
datum. -/
theorem detWeight_eq_of_isPositiveCentralPair (D : RepresentedDegreeDatum W n k)
    (lam : RealWeightCharacter k) {N : ℕ} {z : GL n k} (hz : D.IsPositiveCentralPair N z)
    {U S : Submodule k (n → k)}
    (hU : ∀ w : W, ∀ x ∈ U, D.toRepresentation w x ∈ U)
    (hS : ∀ w : W, ∀ x ∈ S, D.toRepresentation w x ∈ S) (hUS : U < S)
    (hdet : (D.toRepresentation.subquotient hU hS).HasFiniteGeometricDet D.deg)
    (c : kˣ) (hc : ∀ x ∈ S, (z : Matrix n n k) *ᵥ x - (c : k) • x ∈ U) :
    (D.toRepresentation.subquotient hU hS).detWeight lam D.gamma =
      Multiplicative.toAdd (lam c) / N := by
  sorry

end RepresentedDegreeDatum

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- Blueprint `sk-p-tensor`: Tensor-product weights.  Let `V` and `E` be finite-dimensional
representations of one and the same degree datum, and let `Q` be a simple constituent of `V ⊗ E`,
presented as a subquotient `S / U` for invariant submodules `U < S` of `V ⊗ E`.  If `Q` and the
two subquotients produced below have finite geometric determinant, then
`dw_λ(Q) = dw_λ(V_i) + dw_λ(E_j)` for a simple constituent `V_i` of `V` and a simple constituent
`E_j` of `E`; these are the simple quotients of chosen composition series of `V` and `E`.  Neither
`V`, nor `E`, nor `V ⊗ E` is assumed semisimple. -/
theorem exists_detWeight_eq_add_of_subquotient_tprod
    (lam : RealWeightCharacter k) (deg : W →* Multiplicative ℤ) (gamma : W)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (rV : Representation k W V) (rE : Representation k W E)
    {U S : Submodule k (TensorProduct k V E)}
    (hU : ∀ w : W, ∀ x ∈ U, (rV.tprod rE) w x ∈ U)
    (hS : ∀ w : W, ∀ x ∈ S, (rV.tprod rE) w x ∈ S) (hUS : U < S)
    (hsimple : IsIrreducible ((rV.tprod rE).subquotient hU hS))
    (hdet : ((rV.tprod rE).subquotient hU hS).HasFiniteGeometricDet deg) :
    ∃ (UV SV : Submodule k V) (hUV : ∀ w : W, ∀ x ∈ UV, rV w x ∈ UV)
      (hSV : ∀ w : W, ∀ x ∈ SV, rV w x ∈ SV) (UE SE : Submodule k E)
      (hUE : ∀ w : W, ∀ x ∈ UE, rE w x ∈ UE) (hSE : ∀ w : W, ∀ x ∈ SE, rE w x ∈ SE),
      UV < SV ∧ UE < SE ∧
      IsIrreducible (rV.subquotient hUV hSV) ∧ IsIrreducible (rE.subquotient hUE hSE) ∧
      (rV.subquotient hUV hSV).HasFiniteGeometricDet deg ∧
      (rE.subquotient hUE hSE).HasFiniteGeometricDet deg ∧
      ((rV.tprod rE).subquotient hU hS).detWeight lam gamma =
        (rV.subquotient hUV hSV).detWeight lam gamma +
          (rE.subquotient hUE hSE).detWeight lam gamma := by
  sorry

/-- Blueprint `sk-p-exterior`: Exterior-power weights.  Let `V` be a nonzero semisimple
representation of a degree datum, written as an internal direct sum of simple subrepresentations
`Vs j`, and let `wts` be the associated rank-counted weight list: the multiset in which the
determinant weight of `Vs j` occurs `dim Vs j` times.  Fix `1 ≤ s ≤ dim V`.  If the summands
`Vs j` and the simple constituent `Q = S / U` of `⋀^s V` all have finite geometric determinant,
then `dw_λ(Q)` is the sum of a sub-multiset of `wts` of size `s`, that is,
`a_{i₁} + ⋯ + a_{i_s}` for indices `i₁ < ⋯ < i_s` in the rank-counted weight list. -/
theorem exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
    (lam : RealWeightCharacter k) (deg : W →* Multiplicative ℤ) (gamma : W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (rV : Representation k W V) {s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ Module.finrank k V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule k V)
    (hVs : ∀ j, ∀ w : W, ∀ x ∈ Vs j, rV w x ∈ Vs j)
    (hsimpleVs : ∀ j, IsIrreducible (rV.ofInvariant (hVs j)))
    (hdetVs : ∀ j, (rV.ofInvariant (hVs j)).HasFiniteGeometricDet deg)
    (hdirect : DirectSum.IsInternal Vs)
    (wts : Multiset ℝ)
    (hwts : wts = ∑ j : ι, Multiset.replicate (Module.finrank k (Vs j))
      ((rV.ofInvariant (hVs j)).detWeight lam gamma))
    {U S : Submodule k ↥(⋀[k]^s V)}
    (hU : ∀ w : W, ∀ x ∈ U, (rV.exteriorPower s) w x ∈ U)
    (hS : ∀ w : W, ∀ x ∈ S, (rV.exteriorPower s) w x ∈ S) (hUS : U < S)
    (hsimple : IsIrreducible ((rV.exteriorPower s).subquotient hU hS))
    (hdet : ((rV.exteriorPower s).subquotient hU hS).HasFiniteGeometricDet deg) :
    ∃ T : Multiset ℝ, T ≤ wts ∧ Multiset.card T = s ∧
      ((rV.exteriorPower s).subquotient hU hS).detWeight lam gamma = T.sum := by
  sorry

end Representation
