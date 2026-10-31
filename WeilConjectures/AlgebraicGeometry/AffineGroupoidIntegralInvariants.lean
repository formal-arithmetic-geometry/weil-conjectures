/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
import WeilConjectures.AlgebraicGeometry.AffineGroupoidRankwiseMonicGluing
import WeilConjectures.AlgebraicGeometry.AffineGroupoidConstantRankNormAnnihilator

/-!
# Integrality over the invariant ring of an affine groupoid

Source: Stacks Project, Groupoid Schemes, Lemma (Tag 03BJ)
(blueprint: lem-a1-affine-groupoid-integral-invariants).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Transport all groupoid operations along isomorphisms of objects and arrows.
private theorem groupoid_transport {U R U' R' : Scheme.{u}}
    {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R} {c : pullback s t ⟶ R}
    (hG : Scheme.IsGroupoid s t e i c) (α : U' ≅ U) (β : R' ≅ R)
    (s' t' : R' ⟶ U') (hs : s' ≫ α.hom = β.hom ≫ s)
    (ht : t' ≫ α.hom = β.hom ≫ t) :
    ∃ c' : pullback s' t' ⟶ R',
      Scheme.IsGroupoid s' t' (α.hom ≫ e ≫ β.inv) (β.hom ≫ i ≫ β.inv) c' := by
  let L : pullback s' t' ⟶ pullback s t :=
    pullback.map s' t' s t β.hom β.hom α.hom hs ht
  have Lfst {H : Scheme.{u}} (p : H ⟶ pullback s' t') :
      (p ≫ L) ≫ pullback.fst s t = (p ≫ pullback.fst s' t') ≫ β.hom := by
    simp [L, Category.assoc]
  have Lsnd {H : Scheme.{u}} (p : H ⟶ pullback s' t') :
      (p ≫ L) ≫ pullback.snd s t = (p ≫ pullback.snd s' t') ≫ β.hom := by
    simp [L, Category.assoc]
  refine ⟨L ≫ c ≫ β.inv, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, hs, hG.source_id]
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, ht, hG.target_id]
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, hs, ht, hG.source_inv]
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, ht, hs, hG.target_inv]
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, hs, hG.source_comp, L]
  · apply (cancel_mono α.hom).1
    simp [Category.assoc, ht, hG.target_comp, L]
  · intro H a p hp₀ hp₁
    apply (cancel_mono β.hom).1
    have h := hG.id_comp H (a ≫ β.hom) (p ≫ L) (by
      rw [Lfst, hp₀]
      simp [Category.assoc, reassoc_of% ht]) (by rw [Lsnd, hp₁])
    simpa [Category.assoc] using h
  · intro H a p hp₀ hp₁
    apply (cancel_mono β.hom).1
    have h := hG.comp_id H (a ≫ β.hom) (p ≫ L) (by rw [Lfst, hp₀]) (by
      rw [Lsnd, hp₁]
      simp [Category.assoc, reassoc_of% hs])
    simpa [Category.assoc] using h
  · intro H a p hp₀ hp₁
    apply (cancel_mono β.hom).1
    have h := hG.inv_comp H (a ≫ β.hom) (p ≫ L) (by
      rw [Lfst, hp₀]
      simp [Category.assoc]) (by rw [Lsnd, hp₁])
    simpa [Category.assoc, hs, reassoc_of% hs] using h
  · intro H a p hp₀ hp₁
    apply (cancel_mono β.hom).1
    have h := hG.comp_inv H (a ≫ β.hom) (p ≫ L) (by rw [Lfst, hp₀]) (by
      rw [Lsnd, hp₁]
      simp [Category.assoc])
    simpa [Category.assoc, ht, reassoc_of% ht] using h
  · intro H p q r z hpq hr₀ hr₁ hz₀ hz₁
    apply (cancel_mono β.hom).1
    have h := hG.assoc H (p ≫ L) (q ≫ L) (r ≫ L) (z ≫ L) (by
      rw [Lsnd, Lfst, hpq]) (by
      rw [Lfst, hr₀]
      simp [Category.assoc]) (by
      rw [Lsnd, Lsnd, hr₁]) (by
      rw [Lfst, Lfst, hz₀]) (by
      rw [Lsnd, hz₁]
      simp [Category.assoc])
    simpa [Category.assoc] using h

private theorem degree_specMap {U R : Scheme.{u}} [IsAffine U] [IsAffine R]
    (s : R ⟶ U) (r : ℕ) (hs : s.IsFiniteLocallyFreeOfDegree r) :
    (Spec.map s.appTop).IsFiniteLocallyFreeOfDegree r := by
  have := hs
  have heq : Spec.map s.appTop = R.isoSpec.inv ≫ s ≫ U.isoSpec.hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ U.isoSpec.hom) (Scheme.isoSpec_inv_naturality s)
  have : IsFinite (Spec.map s.appTop) := by rw [heq]; infer_instance
  have : Flat (Spec.map s.appTop) := by rw [heq]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map s.appTop) := by rw [heq]; infer_instance
  have : (Spec.map s.appTop).IsFiniteLocallyFree := ⟨⟩
  refine ⟨fun x ↦ ?_⟩
  exact (s.fiberDegree_of_isPullback
    (IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_inv_naturality s |>.symm⟩) x).trans
      (hs.fiberDegree_eq _)

private theorem constantRank_sections_equation {U R : Scheme.{u}}
    [IsAffine U] [IsAffine R] [Nonempty U]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : Scheme.IsGroupoid s t e i c) (r : ℕ) (hr : 0 < r)
    (hs : s.IsFiniteLocallyFreeOfDegree r) (ht : t.IsFiniteLocallyFreeOfDegree r)
    (a : Γ(U, ⊤)) :
    ∃ P : Polynomial (s.appTop.hom.eqLocus t.appTop.hom),
      P.Monic ∧ P.natDegree = r ∧
        P.eval₂ (s.appTop.hom.eqLocus t.appTop.hom).subtype a = 0 := by
  classical
  have : Nontrivial Γ(U, ⊤) :=
    PrimeSpectrum.nontrivial (U.isoSpec.hom (Classical.choice ‹Nonempty U›))
  obtain ⟨c', hG'⟩ := groupoid_transport hG U.isoSpec.symm R.isoSpec.symm
    (Spec.map s.appTop) (Spec.map t.appTop)
    (Scheme.isoSpec_inv_naturality s) (Scheme.isoSpec_inv_naturality t)
  have hs' := degree_specMap s r hs
  have ht' := degree_specMap t r ht
  let P := Algebra.finiteLocallyFreeNormPolynomial s.appTop.hom r hs' (t.appTop.hom a)
  have h := affineGroupoid_constantRank_norm_annihilator Γ(U, ⊤) Γ(R, ⊤)
    s.appTop.hom t.appTop.hom _ _ c' hG' r hr hs' ht' a P rfl
  rcases h with ⟨_, _, hlift, hmonicP, hdegree, _, _, _, _, _, _, _, _, _, _, hroot⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts P).mp hlift
  have hmonic : Q.Monic := Polynomial.monic_of_injective
    (s.appTop.hom.eqLocus t.appTop.hom).subtype_injective (hQ.symm ▸ hmonicP)
  refine ⟨Q, hmonic, ?_, ?_⟩
  · rw [← hmonic.natDegree_map (s.appTop.hom.eqLocus t.appTop.hom).subtype, hQ]
    exact hdegree
  · rw [Polynomial.eval₂_eq_eval_map, hQ]
    exact hroot

/-- An affine groupoid with finite locally free source and target is integral over
its invariant subring. The conclusion spells out a monic annihilator for each element.
Source: Stacks Project, `groupoids.tex`, Tag 03BJ, `lemma-integral-over-invariants`
(blueprint: lem-a1-affine-groupoid-integral-invariants).

Proof:
1. If `Spec A` is empty, `A` is the zero ring and the polynomial `X` annihilates its
   sole element. Otherwise, use `lem-a1-affine-groupoid-invariant-rank-strata` to
   decompose the groupoid into finitely many invariant affine clopen pieces of
   positive constant ranks `r`, with both projections finite locally free of rank `r`.
2. Apply `lem-weil-pbc-sheaf-disjoint-union-product` repeatedly to identify the rings
   of global sections with the finite products of the rings on these pieces.
   Source and target preserve the pieces, so their equalizer is the product of
   the corresponding equalizers `Cᵣ`; this uses only equality in a product.
3. On each piece and for the component `aᵣ` of `a`, apply
   `lem-a1-finite-locally-free-norm-characteristic-polynomial` to the source ring map
   and the target image of `aᵣ`. It gives the monic degree-`r` norm polynomial `Pᵣ`
   of `X - t♯(aᵣ)` and its Cayley--Hamilton annihilation equation in the arrow ring.
4. By `lem-a1-affine-groupoid-polynomial-norm-invariant` applied to `X - aᵣ`, all
   coefficients of `Pᵣ` lie in `Cᵣ`. This does not require globally free modules.
5. Equal source and target images of these coefficients identify the annihilation
   equation with `t♯(Pᵣ(aᵣ)) = 0`. Apply the identity section's ring map, a left
   inverse to `t♯`, to deduce `Pᵣ(aᵣ) = 0`.
6. Let `d` be the largest of the finitely many positive ranks. Multiply each `Pᵣ`
   by `X^(d-r)` to give them the same monic degree `d`. Combine their coefficients
   through the product equalizer from step 2. The resulting polynomial over the
   invariant subring is monic and vanishes at `a`, since it vanishes on every piece. -/
theorem isIntegral_affineGroupoid_invariants
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] :
    ∀ a : A, ∃ P : Polynomial ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom),
      P.Monic ∧
        P.eval₂ ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom).subtype a = 0 := by
  classical
  obtain ⟨I, U, V, s', t', e', i', c', k, C, Cᵣ, ρA, ρB, ρC,
    hpos, hU, hdisj, hcover, hpieces, hC, hCᵣ, hρA, hρB, hmaps, hρC, hglue, hempty⟩ :=
    affineGroupoid_rankwise_monic_gluing A B s t e i c hG
  subst C
  intro a
  by_cases hI : I.Nonempty
  · have hlocal (r : I) : ∃ P : Polynomial (Cᵣ r),
        P.Monic ∧ P.natDegree = r.1 ∧ P.eval₂ (Cᵣ r).subtype (ρA a r) = 0 := by
      have := (hU r).1
      have := (hU r).2.2
      have := (hpieces r).2.2.1
      rw [hCᵣ r]
      exact constantRank_sections_equation (s' r) (t' r) (e' r) (i' r) (c' r)
        (hpieces r).2.2.2.1 r.1 (hpos r)
        (hpieces r).2.2.2.2.1 (hpieces r).2.2.2.2.2.1 (ρA a r)
    choose P hP using hlocal
    obtain ⟨d, Q, hd, hQ, hmonic, hmap, heval, hzero⟩ := hglue a P hI hP
    exact ⟨Q, hmonic, hzero⟩
  · have hemptySpec : IsEmpty (Spec A) := by
      refine ⟨fun x ↦ ?_⟩
      have hbot : (⊤ : (Spec A).Opens) = ⊥ := by
        rw [← hcover]
        apply iSup_eq_bot.mpr
        intro r
        exact False.elim (hI ⟨r.1, r.2⟩)
      have hx : x ∈ (⊥ : (Spec A).Opens) := hbot ▸ (show x ∈ ⊤ from trivial)
      exact hx
    exact ⟨Polynomial.X, (hempty hemptySpec).2.2.1, (hempty hemptySpec).2.2.2 a⟩

end AlgebraicGeometry
