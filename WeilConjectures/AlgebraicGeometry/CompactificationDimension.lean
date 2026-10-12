/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.DimensionDenseOpen

/-!
# Compactifications of the same dimension

An affine scheme of finite type over a field is a quasi-compact open subscheme of a proper
scheme of the same dimension: the scheme-theoretic closure of it in a Nagata compactification.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Compactification without raising the dimension.** An affine scheme `X` of finite type
over a field `k` with `dim X ≤ d` is a quasi-compact open subscheme of a proper `k`-scheme `Y`
with `dim Y ≤ d` (the scheme-theoretic closure of `X` in a Nagata compactification). -/
theorem exists_isProper_isOpenImmersion_topologicalKrullDim_le {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (b : Y ⟶ Spec (.of k)) (j : X ⟶ Y), IsProper b ∧ IsOpenImmersion j ∧
      QuasiCompact j ∧ j ≫ b = a ∧ topologicalKrullDim Y ≤ (d : WithBot ℕ∞) := by
  let c := constructedCompactification a
  obtain ⟨hi, hqc⟩ := isOpenImmersion_constructedCompactification_i a
  have := isProper_constructedCompactification_g a
  refine ⟨c.Z, c.g, c.i, this, hi, hqc, constructedCompactification_i_g a, ?_⟩
  have : IsDominant c.i := by
    have : QuasiCompact (fpEnvelopeCompactification a).i :=
      (fpEnvelopeCompactification a).quasiCompact_openImmersion inferInstance
    rw [(constructedCompactification_spec a).2.1]
    infer_instance
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  refine (topologicalKrullDim_le_of_dense c.g c.i.opensRange c.i.denseRange).trans ?_
  rw [c.i.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range] at hX
  exact hX

end AlgebraicGeometry
