/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverDescent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading

/-!
# Quasi-projectivity descends along field extensions

Over a field `k`, a scheme `X` is quasi-projective precisely when it admits an immersion over
`Spec k` into a projective space `ℙ(β; Spec k)` with finitely many homogeneous coordinates; this
is the form in which quasi-projectivity is phrased here.

## Main definitions

- `AlgebraicGeometry.IsQuasiProjective`: a scheme over a field is quasi-projective if it admits
  an immersion into a projective space.

## Main statements

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`: if the base change `X_K`
  of a `k`-scheme `X` to a field extension `K / k` is quasi-projective over `K`, then `X` is
  quasi-projective over `k` (Stacks 0BDE).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A scheme `X` over a field `k`, with structure morphism `f`, is *quasi-projective* if it
admits an immersion over `Spec k`, that is a locally closed immersion, into a projective space
`ℙ(β; Spec k)` with finitely many homogeneous coordinates; equivalently, an open immersion into
a closed subscheme of such a projective space. (blueprint: `def-sc-quasi-projective`) -/
def IsQuasiProjective {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop :=
  ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
    IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f

/-- **Quasi-projectivity descends along field extensions** (Stacks 0BDE). Let `K / k` be a field
extension and let `X` be a scheme over `k`. If the base change `X_K` admits an immersion over
`Spec K` into a projective space `ℙ(α; Spec K)` with finitely many homogeneous coordinates, then
`X` admits an immersion over `Spec k` into a projective space `ℙ(β; Spec k)` with finitely many
homogeneous coordinates.

The proof follows Stacks 0BDE. The pullback of `𝒪(1)` along the immersion is ample: there is a
morphism `X_K ⟶ ℙ(γ; K)` with affine preimages of the standard opens
(`AlgebraicGeometry.exists_isAffineOpen_preimage_of_isImmersion`). Such a morphism is defined
over a finite extension `k'` of `k`
(`AlgebraicGeometry.exists_finite_isAffineOpen_preimage_standardOpen`); taking norms along
`X_{k'} ⟶ X` gives an ample coordinate cover of `X`
(`AlgebraicGeometry.exists_coordinateCover_of_isPullback`), and an ample coordinate cover of a
scheme of finite type gives an immersion into projective space
(`AlgebraicGeometry.Scheme.CoordinateCover.exists_isImmersion`).

This is an input to the proof of Stacks 0BF7 (`AlgebraicGeometry.GrpObj.exists_isImmersion_
projectiveSpace`), used for blueprint `lem-sc-abelian-variety-projective` and the subsection
`sk-prop-av-projective`. -/
@[stacks 0BDE]
theorem exists_isImmersion_projectiveSpace_of_pullback {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {α : Type u} [Finite α]
    (j : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ ℙ(α; Spec (.of K)))
    [IsImmersion j] (hj : j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K) = pullback.snd _ _) :
    ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
      IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hsurj : Surjective φ := surjective_specMap_algebraMap_of_field
  have hflat : Flat φ := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (pullback.fst f φ) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ hsurj
  have : IsAffineHom (pullback.fst f φ) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  -- `X_K` is of finite type over `K`
  have : IsLocallyNoetherian ℙ(α; Spec (.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : QuasiCompact j := by
    rw [← j.liftCoborder_ι]
    infer_instance
  have : CompactSpace ℙ(α; Spec (.of K)) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : CompactSpace ↥(pullback f φ) := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace ↥(pullback f φ) := quasiSeparatedSpace_of_quasiSeparated j
  have : CompactSpace X := (pullback.fst f φ).surjective.compactSpace (pullback.fst f φ).continuous
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_surjective (pullback.fst f φ)
  have : LocallyOfFiniteType (pullback.snd f φ) := by
    rw [← hj]
    infer_instance
  have : LocallyOfFiniteType f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f φ).flip
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ inferInstance
  -- the pullback of `𝒪(1)` is ample on `X_K`, and this descends to a finite extension of `k`
  obtain ⟨γ, hγ, ψ, hψo, hψ⟩ := exists_isAffineOpen_preimage_of_isImmersion j
  obtain ⟨k', _, _, _, Y, π, q, H, ψ', hψ'⟩ :=
    exists_finite_isAffineOpen_preimage_standardOpen f ψ (hψo.trans hj) hψ
  -- taking norms gives an ample coordinate cover of `X`
  obtain ⟨ι, hι, 𝒟, h𝒟⟩ := exists_coordinateCover_of_isPullback H ψ' hψ'
  exact 𝒟.exists_isImmersion f h𝒟

end AlgebraicGeometry
