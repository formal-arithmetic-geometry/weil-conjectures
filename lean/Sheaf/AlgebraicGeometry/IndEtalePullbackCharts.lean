/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Affine ind-étale charts on a binary fibre product

Source: Bhatt--Scholze, Proposition 2.3.3(4) and Remark 4.1.3.
(blueprint: lem-sfb-indetale-pullback-charts)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pulling back an affine ind-étale refinement of a source affine open preserves
an open cover by affine ind-étale schemes over affine opens of the target.

Source: Bhatt--Scholze, Proposition 2.3.3(4) and Remark 4.1.3; step 4 of
`lem-sfb-weakly-etale-indetale-cech-refinement`.
(blueprint: lem-sfb-indetale-pullback-charts)

Proof: for a point of the fibre product, choose a chart T of P containing its
projection. The projection belongs to the inverse image of the open subscheme A
of U. Inside that inverse image intersected with T, choose an affine open T'
containing the projection. The map T' to T is an open immersion between affines,
hence étale and affine pro-étale. Its composite to the chosen affine open W of V
is therefore affine pro-étale. Form E = T' ×_A D. All three schemes in this
pullback are affine, so E is affine; the projection E to T' is affine pro-étale
by affine base change. Thus E to W is affine pro-étale by composition. The
induced map E to P ×_U D is an open immersion: it is the inverse image of the
open T' in P after identifying the pullback over U with the pullback over A,
using that A to U is a monomorphism. These E cover because T' can be chosen at
every projected point. Their maps to V commute by the pullback identities.
Index by all such affine charts, which lie in the original universe. No
quasi-compactness or finiteness is required for this binary chart construction.
-/
theorem exists_affine_indEtale_pullback_charts
    {U V P A D : Scheme.{u}} (b : U ⟶ V) (p : P ⟶ U)
    (i : A ⟶ U) [IsAffine A] [IsOpenImmersion i]
    (r : D ⟶ A) (hr : proAffineEtale r)
    (T : Scheme.OpenCover.{u} P)
    (hT : ∀ β : T.I₀, IsAffine (T.X β) ∧
      ∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme),
        proAffineEtale g ∧ g ≫ W.ι = T.f β ≫ p ≫ b) :
    ∃ E : Scheme.OpenCover.{u} (pullback p (r ≫ i)),
      ∀ β : E.I₀, IsAffine (E.X β) ∧
        ∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : E.X β ⟶ W.toScheme),
          proAffineEtale g ∧
          g ≫ W.ι = E.f β ≫ pullback.fst p (r ≫ i) ≫ p ≫ b := by
  classical
  have hD : IsAffine D := hr.isAffine
  let B : Scheme.OpenCover.{u} (pullback p i) := T.pullbackCoverOfLeft p i
  let S : Scheme.OpenCover.{u} (pullback p i) := B.affineRefinement.openCover
  let E : Scheme.OpenCover.{u} (pullback (pullback.snd p i) r) :=
    S.pullbackCoverOfLeft (pullback.snd p i) r
  let e := pullbackLeftPullbackSndIso p i r
  refine ⟨E.pushforwardIso e.hom, ?_⟩
  intro β
  rcases β with ⟨a, j⟩
  obtain ⟨hA, W, hW, g, hg, he⟩ := hT a
  have hS : IsAffine (S.X ⟨a, j⟩) := inferInstance
  let v : S.X ⟨a, j⟩ ⟶ T.X a :=
    (B.X a).affineCover.f j ≫ pullback.fst (T.f a ≫ p) i
  have hv : IsOpenImmersion v := by dsimp [v]; infer_instance
  have hvpro : proAffineEtale v := proAffineEtale.of_isAffine v
  let q : E.X ⟨a, j⟩ ⟶ S.X ⟨a, j⟩ :=
    pullback.fst (S.f ⟨a, j⟩ ≫ pullback.snd p i) r
  have hq : proAffineEtale q :=
    MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
      (IsPullback.of_hasPullback (S.f ⟨a, j⟩ ≫ pullback.snd p i) r).flip hr
  have hE : IsAffine (E.X ⟨a, j⟩) := hq.isAffine
  refine ⟨hE, W, hW, q ≫ v ≫ g,
    proAffineEtale.comp_mem _ _ hq (proAffineEtale.comp_mem _ _ hvpro hg), ?_⟩
  change (q ≫ v ≫ g) ≫ W.ι =
    (E.f ⟨a, j⟩ ≫ e.hom) ≫ pullback.fst p (r ≫ i) ≫ p ≫ b
  dsimp only [e]
  simp only [Category.assoc, he, pullbackLeftPullbackSndIso_hom_fst_assoc]
  change q ≫ v ≫ T.f a ≫ p ≫ b =
    E.f ⟨a, j⟩ ≫ pullback.fst (pullback.snd p i) r ≫ pullback.fst p i ≫ p ≫ b
  have hEf : E.f ⟨a, j⟩ ≫ pullback.fst (pullback.snd p i) r =
      q ≫ S.f ⟨a, j⟩ := by
    exact pullback.lift_fst _ _ _
  have hSf : S.f ⟨a, j⟩ ≫ pullback.fst p i = v ≫ T.f a := by
    change ((B.X a).affineCover.f j ≫ B.f a) ≫ pullback.fst p i = v ≫ T.f a
    dsimp only [v]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ (B.X a).affineCover.f j ≫ z)
      (pullback.lift_fst _ _ _)
  rw [← Category.assoc (E.f ⟨a, j⟩), hEf]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ q ≫ z ≫ p ≫ b) hSf.symm


end AlgebraicGeometry
