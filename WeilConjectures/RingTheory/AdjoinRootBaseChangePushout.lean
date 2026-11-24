/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Category.Ring.Constructions

/-! # Adjoining a root commutes with base change

For a ring map `α : R →+* S` and `F : R[X]`, the square formed by `R → S`, `R → R[X]/(F)`,
`S → S[X]/(F.map α)` and `R[X]/(F) → S[X]/(F.map α)` is a pushout in `CommRingCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace CommRingCat

/-- For `α : R →+* S` and `F : R[X]`, the square with sides `α`, `AdjoinRoot.of F`,
`AdjoinRoot.of (F.map α)` and `AdjoinRoot.map α F (F.map α)` is a pushout in `CommRingCat`. -/
theorem isPushout_adjoinRoot_map {R S : Type u} [CommRing R] [CommRing S]
    (α : R →+* S) (F : R[X]) :
    IsPushout (ofHom α) (ofHom (AdjoinRoot.of F))
      (ofHom (AdjoinRoot.of (F.map α)))
      (ofHom (AdjoinRoot.map α F (F.map α) dvd_rfl)) := by
  let β := AdjoinRoot.map α F (F.map α) dvd_rfl
  have hw : ofHom α ≫ ofHom (AdjoinRoot.of (F.map α)) =
      ofHom (AdjoinRoot.of F) ≫ ofHom β := by
    ext r
    simp [β]
  refine ⟨⟨hw⟩, ⟨PushoutCocone.isColimitAux' _ (fun s ↦ ?_)⟩⟩
  have hcomm : s.inl.hom.comp α = s.inr.hom.comp (AdjoinRoot.of F) := by
    exact congrArg Hom.hom s.condition
  have hroot : (F.map α).eval₂ s.inl.hom (s.inr (AdjoinRoot.root F)) = 0 := by
    rw [Polynomial.eval₂_map, hcomm]
    rw [← Polynomial.hom_eval₂]
    simp [AdjoinRoot.eval₂_root]
  let l := AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root F)) hroot
  refine ⟨ofHom l, ?_, ?_, ?_⟩
  · ext r
    exact AdjoinRoot.lift_of hroot
  · apply Hom.ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change l (β (AdjoinRoot.of F r)) = s.inr (AdjoinRoot.of F r)
      rw [show β (AdjoinRoot.of F r) = AdjoinRoot.of (F.map α) (α r) by simp [β]]
      rw [AdjoinRoot.lift_of]
      exact DFunLike.congr_fun hcomm r
    · change l (β (AdjoinRoot.root F)) = s.inr (AdjoinRoot.root F)
      simp [β, l]
  · intro k hk₁ hk₂
    apply Hom.ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change k (AdjoinRoot.of (F.map α) r) = l (AdjoinRoot.of (F.map α) r)
      rw [AdjoinRoot.lift_of]
      exact congrArg (fun z : of S ⟶ s.pt ↦ z r) hk₁
    · have h := congrArg (fun z : of (AdjoinRoot F) ⟶ s.pt ↦
          z (AdjoinRoot.root F)) hk₂
      change k (β (AdjoinRoot.root F)) = s.inr (AdjoinRoot.root F) at h
      rw [show β (AdjoinRoot.root F) = AdjoinRoot.root (F.map α) by
        exact AdjoinRoot.map_root ..] at h
      change k (AdjoinRoot.root (F.map α)) = l (AdjoinRoot.root (F.map α))
      rw [AdjoinRoot.lift_root]
      exact h

/-- Variant of `isPushout_adjoinRoot_map` with `F.map α` replaced by a polynomial `G` equal to
it. -/
theorem isPushout_adjoinRoot_map_eq {R S : Type u} [CommRing R] [CommRing S]
    (α : R →+* S) (F : R[X]) (G : S[X]) (h : F.map α = G) :
    IsPushout (ofHom α) (ofHom (AdjoinRoot.of F))
      (ofHom (AdjoinRoot.of G))
      (ofHom (AdjoinRoot.map α F G h.symm.dvd)) := by
  subst G
  exact isPushout_adjoinRoot_map α F

end CommRingCat
