/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Quasi-compact clopen pieces of split local schemes are finite

Source: the finite-sheet argument of `lem-sf-normal-strict-local-split-components`, step 6
(blueprint: lem-sf-split-local-clopen-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact clopen piece of a coproduct of copies of a local affine scheme is
finite over that affine scheme.

Source: blueprint `thm-lisse-qlbar-representations`, proof (4), finite-sheet argument
(blueprint: lem-sf-split-local-clopen-finite).

Proof: the inverse image of the clopen piece in each connected sheet is either empty
or the whole sheet. The surviving sheets give a disjoint open cover of the piece.
It is quasi-compact, so finitely many sheets cover it. Their cofan is colimiting by
disjoint open gluing; its structure map is a finite coproduct of identities and hence finite.
This includes the empty clopen piece and an empty indexing type.
-/
theorem isFinite_clopen_of_coproduct_sections
    (R : CommRingCat.{u}) [IsLocalRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec R) {I : Type u} (ι : I → (Spec R ⟶ Y))
    (hι : ∀ i, ι i ≫ p = 𝟙 (Spec R))
    (hc : Nonempty (IsColimit (Cofan.mk Y ι)))
    (U : Y.Opens) (hclosed : IsClosed (U : Set Y))
    [QuasiCompact (U.ι ≫ p)] : IsFinite (U.ι ≫ p) := by
  classical
  let F : I → Scheme.{u} := fun _ ↦ Spec R
  have : IsIso (Sigma.desc ι) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Y ι)).mp hc
  have hi (i : I) : IsOpenImmersion (ι i) := by
    have hfac : ι i = Sigma.ι F i ≫ Sigma.desc ι := by simp [F]
    rw [hfac]
    infer_instance
  let (i : I) : IsOpenImmersion (ι i) := hi i
  have hcover (y : Y) : ∃ i x, ι i x = y := by
    obtain ⟨w, rfl⟩ := (Sigma.desc ι).surjective y
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk F).surjective w
    refine ⟨i, x, ?_⟩
    rw [sigmaMk_mk]
    change ι i x = (Sigma.ι F i ≫ Sigma.desc ι) x
    rw [Sigma.ι_desc]
  have hindex {i j : I} (x y : Spec R) (h : ι i x = ι j y) : i = j := by
    have he : (Sigma.ι F i) x = (Sigma.ι F j) y := by
      apply (Sigma.desc ι).isOpenEmbedding.injective
      change (Sigma.ι F i ≫ Sigma.desc ι) x = (Sigma.ι F j ≫ Sigma.desc ι) y
      simpa only [Sigma.ι_desc] using h
    exact congrArg Sigma.fst ((sigmaι_eq_iff F i j x y).mp he)
  let J := {i : I // (ι i ⁻¹' (U : Set Y)).Nonempty}
  have hpre (i : J) : ι i.val ⁻¹' (U : Set Y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := i.2
    have hc := (IsLocalRing.specializes_closedPoint y).mem_closed
      (hclosed.preimage (ι i.val).continuous) hy
    exact (IsLocalRing.specializes_closedPoint x).mem_open
      (U.isOpen.preimage (ι i.val).continuous) hc
  let σ (i : J) : Spec R ⟶ U.toScheme := IsOpenImmersion.lift U.ι (ι i.val) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.eq_univ_iff_forall.mp (hpre i) x)
  have hσ (i : J) : σ i ≫ U.ι = ι i.val := IsOpenImmersion.lift_fac _ _ _
  have hσopen (i : J) : IsOpenImmersion (σ i) := by
    have : IsOpenImmersion (σ i ≫ U.ι) := hσ i ▸ hi i.val
    exact IsOpenImmersion.of_comp _ U.ι
  let (i : J) : IsOpenImmersion (σ i) := hσopen i
  have hσcover (y : U.toScheme) : ∃ i : J, y ∈ Set.range (σ i) := by
    obtain ⟨i, x, hx⟩ := hcover (U.ι y)
    let j : J := ⟨i, x, by
      change ι i x ∈ (U : Set Y)
      rw [hx]
      exact y.2⟩
    refine ⟨j, x, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    change (σ j ≫ U.ι) x = U.ι y
    rw [hσ]
    exact hx
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ p)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : J ↦ Set.range (σ i)) (fun i ↦ (σ i).isOpenEmbedding.isOpen_range)
    (fun y _ ↦ Set.mem_iUnion.mpr (hσcover y))
  let τ (i : s) : Spec R ⟶ U.toScheme := σ i.val
  have hτcover : ⨆ i : s, (τ i).opensRange = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi, hiy⟩ : ∃ i ∈ s, y ∈ Set.range (σ i) := by
      simpa using hs (Set.mem_univ y)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hiy⟩
  have hτdisj : Pairwise (fun i j : s ↦ Disjoint (τ i).opensRange (τ j).opensRange) := by
    intro i j hij
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro y ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
    apply hij
    apply Subtype.ext
    apply Subtype.ext
    apply hindex x z
    have h := congrArg U.ι (hx.trans hz.symm)
    change (σ i.val ≫ U.ι) x = (σ j.val ≫ U.ι) z at h
    simpa [hσ] using h
  have hcτ := nonempty_isColimit_cofanMk_of τ hτcover hτdisj
  have : IsIso (Sigma.desc τ) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk U.toScheme τ)).mp hcτ
  have hτ (i : s) : τ i ≫ (U.ι ≫ p) = 𝟙 (Spec R) := by
    rw [← Category.assoc, hσ]
    exact hι i.val.val
  have hdesc : Sigma.desc τ ≫ (U.ι ≫ p) = Sigma.desc (fun _ : s ↦ 𝟙 (Spec R)) := by
    ext i
    simpa using hτ i
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite (Sigma.desc τ), hdesc]
  infer_instance

end AlgebraicGeometry
