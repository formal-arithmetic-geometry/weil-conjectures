/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.AlgebraicGeometry.DenseCompactification
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Dimension of schemes of finite type over a field

The dimension of a scheme is `topologicalKrullDim` of its underlying space (blueprint
`def-kun-dimension`).

## Main results

- `AlgebraicGeometry.topologicalKrullDim_lt_top_of_finiteType` (blueprint
  `lem-kun-dimension-finite-type`): a scheme of finite type over a field has finite dimension.
- `AlgebraicGeometry.topologicalKrullDim_pullback_eq_and_eq_of_isOpenImmersion` (blueprint
  `lem-kun-dimension-extension`): the dimension of a scheme of finite type over a field is
  invariant under extension of the base field and under passing to a dense open subscheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- The spectrum of a finitely generated algebra over a field `k` has dimension at most the
number of generators: it is a quotient of a polynomial ring in finitely many variables. -/
theorem exists_topologicalKrullDim_spec_le_of_field {k : Type u} [Field k] {A : CommRingCat.{u}}
    (p : Spec A ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    ∃ n : ℕ, topologicalKrullDim (Spec A) ≤ n := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have hφ : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hφ
  refine ⟨n, (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans_le
    ((ringKrullDim_le_of_surjective f.toRingHom hf).trans ?_)⟩
  simp

/-- Blueprint `lem-kun-dimension-finite-type`: **a scheme of finite type over a field has finite
dimension.** If `X` is of finite type over a field `K`, then `dim X < ∞`: `X` is covered by
finitely many affine opens `Spec A`, with `A` a quotient of a polynomial ring in finitely many
variables, hence of finite dimension. -/
theorem topologicalKrullDim_lt_top_of_finiteType {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] :
    topologicalKrullDim X < ⊤ := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  let 𝒰 := X.affineCover.finiteSubcover
  choose n hn using fun i : 𝒰.I₀ ↦ exists_topologicalKrullDim_spec_le_of_field (𝒰.f i ≫ a)
  have hle (i : 𝒰.I₀) : n i ≤ ∑ i, n i :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  refine lt_of_le_of_lt (topologicalKrullDim_le_of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange)
    𝒰.iSup_opensRange (∑ i, n i : ℕ) fun i ↦ ?_) ?_
  · exact ((𝒰.f i).isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm.trans_le
      (hn i)).trans (by exact_mod_cast hle i)
  · exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)


end AlgebraicGeometry
