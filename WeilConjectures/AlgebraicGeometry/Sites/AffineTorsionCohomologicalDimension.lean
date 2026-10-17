/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension

/-!
# The affine Artin vanishing bound

Let `K` be a field with `cd_tor(K) ≤ c` and `X` an affine `K`-scheme of finite type. Then
`cd_tor(X) ≤ dim X + c` (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`,
blueprint `thm-sc-affine-torsion-cd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The case `d = 0` of `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`:
an affine `K`-scheme of finite type and dimension zero is finite over `K`, so its torsion
cohomological dimension is at most that of `K`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isFinite`). -/
lemma hasTorsionCohomologicalDimensionLE_of_isAffine_of_topologicalKrullDim_le_zero {K : Type u}
    [Field K] {c : ℕ} (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ 0) :
    X.HasTorsionCohomologicalDimensionLE c := by
  have : QuasiCompact a := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hX
  have : LocallyQuasiFinite a := locallyQuasiFinite_iff_isDiscrete_preimage_singleton.2
    fun _ ↦ IsDiscrete.univ.mono (Set.subset_univ _)
  have : IsLocallyArtinian (Spec (.of K)) := isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsFinite a := IsFinite.of_locallyQuasiFinite a
  exact hK.of_isFinite a

/-- The case `d = 1` of `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`:
over an algebraic closure `K̄` of `K`, `X_K̄` is an affine curve, so `cd_tor(X_K̄) ≤ 1`
(`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`), and
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure` concludes. -/
lemma hasTorsionCohomologicalDimensionLE_of_isAffine_of_topologicalKrullDim_le_one {K : Type u}
    [Field K] {c : ℕ} (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ 1) :
    X.HasTorsionCohomologicalDimensionLE (1 + c) := by
  have : QuasiCompact a := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : IsCurve (pullback.snd a g) :=
    { krullDim_le_one := (topologicalKrullDim_pullback_le_of_field a g).trans hX }
  rw [add_comm]
  exact hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure (AlgebraicClosure K) a hK
    ((IsCurve.hasTorsionCohomologicalDimensionLE (pullback.snd a g)).2 inferInstance)

/-- Blueprint `thm-sc-affine-torsion-cd`: The affine torsion cohomological dimension bound.

Let `K` be a field with `cd_tor(K) ≤ c`, and let `X` be an affine `K`-scheme of finite type
(structure morphism `a`) of dimension at most `d`. Then `cd_tor(X) ≤ d + c`:
`Hᵠ(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > d + c`.

The proof is by induction on `d`, over all ground fields at once; it reduces to algebraically
closed `K` (`lem-sc-cd-ground-field`) and, by Noether normalisation, to affine space, where the
Leray spectral sequence of `𝔸ᵈ ⟶ ℙ¹ × 𝔸ᵈ⁻¹ ⟶ 𝔸ᵈ⁻¹` and a computation of the stalks of the
higher direct images (`lem-sc-one-variable-field-cd`, `lem-sc-cd-affine-limit`) conclude. -/
theorem hasTorsionCohomologicalDimensionLE_of_isAffine {K : Type u} [Field K] {c d : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) :=
  sorry

end AlgebraicGeometry.Scheme
