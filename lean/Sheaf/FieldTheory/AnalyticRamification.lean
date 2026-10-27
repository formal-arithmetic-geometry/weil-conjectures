/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Sheaf.GroupTheory.RationalRank

/-!
# Numerical ramification for real nonarchimedean norms

Source: Temkin, Stable modification of relative curves, §2.1, notation and
Lemma 2.1.5 (blueprint: def-trf-analytic-ramification).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped NNReal

universe u v

namespace AnalyticRamification

/-- The actual ring of elements of norm at most one.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
abbrev integers (K : Type u) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K := (NormedField.valuation (K := K)).valuationSubring

/-- The quotient of the norm valuation ring by its maximal ideal.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
abbrev residue (K : Type u) [NormedField K] [IsUltrametricDist K] :=
  IsLocalRing.ResidueField (integers K)

/-- The subgroup of positive real values of nonzero field elements.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
def values (K : Type u) [NormedField K] [IsUltrametricDist K] : Subgroup (ℝ≥0)ˣ :=
  (Units.map (NormedField.valuation (K := K)).toMonoidHom).range

/-- The restriction of a norm-preserving field embedding to integer rings.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
def integerMap {K : Type u} {L : Type v} [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L]
    (f : K →+* L) (hf : ∀ x : K, ‖f x‖ = ‖x‖) : integers K →+* integers L :=
  f.restrict (integers K) (integers L) (fun x hx ↦
    (show ‖f x‖ ≤ 1 from (hf x).symm ▸ hx))

/-- Norm-preserving field embeddings reflect units in their integer rings.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification).
Proof: an integral element is a unit precisely when its norm is one; preservation
of the norm therefore reflects this condition. Equivalently its inverse remains integral. -/
theorem integerMap_isLocalHom {K : Type u} {L : Type v}
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    (f : K →+* L) (hf : ∀ x : K, ‖f x‖ = ‖x‖) :
    IsLocalHom (integerMap f hf) := by
  sorry

/-- The canonical map sends the residue of x to the residue of f(x).
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
noncomputable def residueMap {K : Type u} {L : Type v}
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    (f : K →+* L) (hf : ∀ x : K, ‖f x‖ = ‖x‖) : residue K →+* residue L :=
  @IsLocalRing.ResidueField.map _ _ _ _ _ _ (integerMap f hf)
    (integerMap_isLocalHom f hf)

/-- The canonical residue scalar action.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
@[instance_reducible]
noncomputable def residueAlgebra {K : Type u} {L : Type v}
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    (f : K →+* L) (hf : ∀ x : K, ‖f x‖ = ‖x‖) : Algebra (residue K) (residue L) :=
  (residueMap f hf).toAlgebra

/-- Index of the ground value group in the upper value group (zero for infinite index).
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
noncomputable def ramificationIndex (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L] : ℕ :=
  (values K).relIndex (values L)

/-- Residue-field degree, with the canonical residue embedding.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
noncomputable def residueDegree (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : ℕ :=
  @Module.finrank (residue K) (residue L) _ _
    (residueAlgebra (algebraMap K L) (norm_algebraMap' L)).toModule

/-- The rational-valued defect n/(ef), before integrality is proved.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
noncomputable def defect (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : ℚ :=
  (Module.finrank K L : ℚ) / (ramificationIndex K L * residueDegree K L : ℕ)

/-- Immediacy means equality of actual value groups and surjectivity on residues.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
def IsImmediate (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : Prop :=
  values K = values L ∧
    Function.Surjective (residueMap (algebraMap K L) (norm_algebraMap' L))

/-- Separability of the canonical residue extension, using Mathlib separability.
Source: Temkin §2.1 (blueprint: def-trf-analytic-ramification). -/
def HasSeparableResidue (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : Prop :=
  @Algebra.IsSeparable (residue K) (residue L) _ _
    (residueAlgebra (algebraMap K L) (norm_algebraMap' L))

/-- The numerical unramified criterion e=d=1 with separable residues.
Source: Temkin Lemma 2.1.5(ii) (blueprint: def-trf-analytic-ramification). -/
def IsUnramified (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : Prop :=
  ramificationIndex K L = 1 ∧ defect K L = 1 ∧ HasSeparableResidue K L

/-- The numerical tame criterion; characteristic zero has no index restriction.
Source: Temkin Lemma 2.1.5(iii) (blueprint: def-trf-analytic-ramification). -/
def IsTame (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : Prop :=
  defect K L = 1 ∧ HasSeparableResidue K L ∧
    (ringChar (residue K) = 0 ∨ (ramificationIndex K L).Coprime (ringChar (residue K)))

/-- Cardinal rational rank of the relative value group.
Source: Temkin §2.1, E invariant (blueprint: def-trf-analytic-ramification). -/
noncomputable def relativeRationalRank (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L] :
    Cardinal :=
  AddCommGroup.rationalRank (Additive (values L ⧸ (values K).subgroupOf (values L)))

/-- Cardinal transcendence degree of the relative residue extension.
Source: Temkin §2.1, F invariant (blueprint: def-trf-analytic-ramification). -/
noncomputable def residueTrdeg (K : Type u) (L : Type v)
    [NormedField K] [NormedField L] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra K L] : Cardinal :=
  @Algebra.trdeg (residue K) (residue L) _ _
    (residueAlgebra (algebraMap K L) (norm_algebraMap' L))

end AnalyticRamification
