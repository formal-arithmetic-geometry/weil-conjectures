/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Determinant weights of a degree datum

A *real weight character* is a homomorphism `λ : k^× → (ℝ, +)`.  Composing it with the
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

* `Representation.RealWeightCharacter`: a homomorphism `k^× → (ℝ, +)`.
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
  constituents of an exterior power.

## Blueprint

`Representation.RealWeightCharacter`, `Representation.HasFiniteGeometricDet`,
`Representation.detWeight` and `Representation.detWeight_mul_of_mem_ker` implement `sk-d-weights`;
`RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair` implements `sk-p-readout`;
`Representation.exists_detWeight_eq_add_of_subquotient_tprod` implements `sk-p-tensor`;
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower` implements
`sk-p-exterior`.
-/

@[expose] public section

open scoped Matrix Zariski

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- A *real weight character* is a group homomorphism `λ` from the units of `k` to the reals
under addition.
(blueprint: `sk-d-weights`) -/
abbrev RealWeightCharacter (k : Type*) [Field k] := kˣ →* Multiplicative ℝ

/-- A representation has *finite geometric determinant* for a degree homomorphism `deg` when its
determinant character takes only finitely many values on the degree-zero subgroup `P = ker deg`.
(blueprint: `sk-d-weights`) -/
def HasFiniteGeometricDet (deg : W →* Multiplicative ℤ) (ρ : Representation k W V) : Prop :=
  (Set.range fun w : deg.ker ↦ ρ.detCharacter w).Finite

/-- The *determinant weight* of a representation with respect to a real weight character `χ` and
a degree-one element `γ` is `dw_χ(ρ) = χ(δ(γ)) / dim V`.
(blueprint: `sk-d-weights`) -/
noncomputable def detWeight (χ : RealWeightCharacter k) (γ : W) (ρ : Representation k W V) : ℝ :=
  Multiplicative.toAdd (χ (ρ.detCharacter γ)) / Module.finrank k V

/-- The determinant weight does not depend on the chosen degree-one element: replacing `γ` by
`u γ` for a degree-zero element `u` leaves it unchanged, because the determinant character takes
finitely many values on the degree-zero subgroup and `ℝ` is torsion-free.
(blueprint: `sk-d-weights`) -/
theorem detWeight_mul_of_mem_ker {deg : W →* Multiplicative ℤ} (ρ : Representation k W V)
    (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealWeightCharacter k) (γ : W) {u : W}
    (hu : u ∈ deg.ker) : ρ.detWeight χ (u * γ) = ρ.detWeight χ γ := by
  sorry

/-- The rank-counted weight multiset of a family of subrepresentations: the determinant weight of
`Vs j` occurs `dim Vs j` times. -/
noncomputable def weightMultiset {ι : Type*} [Fintype ι] {ρ : Representation k W V}
    (χ : RealWeightCharacter k) (γ : W) (Vs : ι → Subrepresentation ρ) : Multiset ℝ :=
  ∑ j : ι, Multiset.replicate (Module.finrank k (Vs j).toSubmodule)
    ((Vs j).toRepresentation.detWeight χ γ)

end Representation

namespace RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Fix a real weight character `χ` and a positive central pair `(N, z)` for a represented degree
datum.  If a nonzero `W`-subquotient `Q = S / U` of the defining representation has finite
geometric determinant and `z` acts on `Q` as the scalar `c`, then `dw_χ(Q) = χ(c) / N`.  The
scalar hypothesis is automatic when `Q` is simple, by Schur's lemma.
(blueprint: `sk-p-readout`) -/
theorem detWeight_eq_of_isPositiveCentralPair (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealWeightCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) {U S : Subrepresentation D.asRepresentation} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) (c : kˣ)
    (hc : ∀ x ∈ S, Matrix.toLinAlgEquiv' (z : Matrix n n k) x - (c : k) • x ∈ U) :
    (S.subquotient U).detWeight χ D.degreeOneElement =
      Multiplicative.toAdd (χ c) / N := by
  sorry

end RepresentedDegreeDatum

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
    (χ : RealWeightCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
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

/-- Let `V` be a nonzero semisimple representation of a degree datum, written as an internal
direct sum of simple subrepresentations `Vs j`, with rank-counted weight multiset
`Representation.weightMultiset χ γ Vs`: the multiset in which the determinant weight of `Vs j`
occurs `dim Vs j` times.  If the summands `Vs j` and the simple constituent `Q = S / U` of
`⋀^s V` all have finite geometric determinant, then `dw_χ(Q)` is the sum of a sub-multiset of the
weight multiset of size `s`, that is, `a_{i₁} + ⋯ + a_{i_s}` for indices `i₁ < ⋯ < i_s` in the
rank-counted weight list.
(blueprint: `sk-p-exterior`) -/
theorem exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
    (χ : RealWeightCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
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
  sorry

end Representation
