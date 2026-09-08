/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine schemes of finite type over a base embed into projective space

Let `S` be a scheme and let `g : V ⟶ S` be a morphism that is locally of finite type, with `V`
affine. We construct a finite index type `n` and an immersion `V ⟶ ℙ(n; S)` over `S`.

The construction is elementary. Cover `V` by finitely many basic opens `V_{b l}` each lying
over an affine open `W l` of `S`. Since `V_{b l} ⟶ W l` is a morphism of affine schemes of
finite type, the ring `Γ(V_{b l}, ⊤)` is generated over `Γ(W l, ⊤)` by finitely many fractions
with denominator a power of `b l`; multiplying numerators by `b l` and adding the fraction
`1 / b l` to the family, one gets a finite family `t l` of global sections of `V` such that
`Γ(V_{b l}, ⊤)` is generated over `Γ(W l, ⊤)` by the quotients `t l μ / b l`.

Taking for `n` the disjoint union of the index set of the cover with the index sets of these
families, and for `s : n → Γ(V, ⊤)` the sections `b l` and `t l μ`, the morphism
`j := ProjectiveSpace.homOfSections g s` restricts on the standard chart `D₊(T_{b l})` to the
morphism into affine space over `S` classified by the quotients `s i / b l`. This factors
through the affine space over `W l`, where it is `Spec` of a surjection of rings, hence a closed
immersion; composing with the open immersion `𝔸(m; W l) ⟶ 𝔸(m; S)` shows the restriction of `j`
is an immersion. Since the standard charts used cover the image of `j`, this proves `j` is an
immersion.

## Main results

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace` — an affine scheme locally of finite
  type over `S` admits an immersion over `S` into a projective space `ℙ(n; S)` with `n` finite.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {V S : Scheme.{u}}

/-- **An affine scheme locally of finite type over `S` admits an immersion into a projective
space over `S`.** -/
theorem exists_isImmersion_projectiveSpace [IsAffine V] (g : V ⟶ S) [LocallyOfFiniteType g] :
    ∃ (n : Type u) (_ : Finite n) (j : V ⟶ ℙ(n; S)),
      IsImmersion j ∧ j ≫ ℙ(n; S) ↘ S = g := by
  obtain ⟨Λ, hΛ, b, W, hW, hWle, hcov⟩ :=
    exists_finite_basicOpen_cover_le_preimage_isAffineOpen g
  have : Finite Λ := hΛ
  choose k t ht using fun l : Λ ↦
    exists_finite_subring_closure_divBasicOpen_eq_top g (b l) (W l) (hW l) (hWle l)
  let n : Type u := Λ ⊕ (Σ l : Λ, Fin (k l))
  let s : n → Γ(V, ⊤) := Sum.elim b fun p ↦ t p.1 p.2
  have hs : Ideal.span (Set.range s) = ⊤ := by
    rw [← (isAffineOpen_top V).iSup_basicOpen_eq_self_iff, iSup_range']
    exact top_le_iff.mp
      (hcov.ge.trans (iSup_le fun l ↦ le_iSup (fun i ↦ V.basicOpen (s i)) (Sum.inl l)))
  have hpre (l : Λ) : ProjectiveSpace.homOfSections g s hs ⁻¹ᵁ
      ProjectiveSpace.standardOpen n S (Sum.inl l) = V.basicOpen (s (Sum.inl l)) :=
    ProjectiveSpace.homOfSections_preimage_standardOpen g s hs (Sum.inl l)
  refine ⟨n, inferInstance, ProjectiveSpace.homOfSections g s hs, ?_,
    ProjectiveSpace.homOfSections_over g s hs⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun l : Λ ↦ ProjectiveSpace.standardOpen n S (Sum.inl l)) ?_ fun l ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ l : Λ, V.basicOpen (b l) := by
      rw [hcov]
      trivial
    obtain ⟨l, hxl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨l, ?_⟩)
    rw [← Scheme.Hom.mem_preimage, hpre l]
    exact hxl
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr (ProjectiveSpace.homOfSections g s hs)
        (U := ProjectiveSpace.standardOpen n S (Sum.inl l)) le_rfl rfl (hpre l) @IsImmersion,
      ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
        (ProjectiveSpace.standardOpenIso n S (Sum.inl l)).hom,
      ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom g s hs (Sum.inl l)]
    refine AffineSpace.isImmersion_homOfVector_divBasicOpen g s (Sum.inl l) (W l) (hW l) (hWle l)
      (eq_top_iff.mpr ((ht l).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
    rintro _ ⟨μ, rfl⟩
    exact ⟨⟨Sum.inr ⟨l, μ⟩, Sum.inr_ne_inl⟩, rfl⟩

end AlgebraicGeometry
