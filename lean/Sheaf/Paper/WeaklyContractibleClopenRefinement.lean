/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Limits

/-! # Finite clopen refinement from categorical weak contractibility

Source: Stacks Project, proetale.tex, Tag 098F, covering implication.
(blueprint: lem-sf-weakly-contractible-clopen-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u v
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private theorem section_of_cover
    {X : Scheme.{u}} {W V : X.ProEt} (p : V ⟶ W)
    (hp : Sieve.generate (Presieve.singleton p) ∈ ProEt.topology X W)
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    ∃ s : W ⟶ V, s ≫ p = 𝟙 W := by
  let J := ProEt.topology X
  have hepi : Epi (J.uliftYoneda.{u + 1}.map p) := by
    constructor
    intro Z a b hab
    apply J.uliftYonedaEquiv.injective
    have heq : Z.obj.map p.op (J.uliftYonedaEquiv a) =
        Z.obj.map p.op (J.uliftYonedaEquiv b) := by
      rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality, hab]
    apply Sheaf.isSeparated Z W _ hp
    rintro T f ⟨_, g, _, ⟨⟩, rfl⟩
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (Z.obj.map g.op) heq
  obtain ⟨s, hs⟩ := hW (J.uliftYoneda.{u + 1}.map p)
    ((Sheaf.isLocallySurjective_iff_epi _).mpr hepi) ⟨𝟙 W⟩
  exact ⟨s.down, congrArg ULift.down hs⟩

/-- A pro-etale covering of a categorically weakly contractible affine refines to
finitely many disjoint clopen subschemes, with maps to selected covering members.

Source: Stacks Project, proetale.tex, Tag 098F, covering implication
(blueprint: lem-sf-weakly-contractible-clopen-refinement).

Proof: quasi-compactness selects finitely many affine opens in the covering
members. Their disjoint union covers S. Its representable maps epimorphically to
the terminal representable, so weak contractibility supplies a section. Inverse
images of the coproduct components along that section form the clopen partition.
The restricted section supplies the required factorizations. Discard empty parts;
the empty target consequently has the empty partition. -/
theorem weakly_contractible_clopen_refinement
    (S : Scheme.{u}) [IsAffine S]
    (hweak : (ProEt.topology S).IsWeaklyContractible.{u + 1} (ProEt.mk (𝟙 S)))
    (I : Type v) (V : I → S.ProEt) (a : ∀ i : I, V i ⟶ ProEt.mk (𝟙 S))
    (hcover : Presieve.ofArrows V a ∈ ProEt.precoverage S (ProEt.mk (𝟙 S))) :
    ∃ (m : ℕ) (W : Fin m → S.Opens),
      (∀ k : Fin m, IsClosed (W k : Set S)) ∧
      (∀ k : Fin m, (W k : Set S).Nonempty) ∧
      Pairwise (fun j k : Fin m ↦ Disjoint (W j) (W k)) ∧
      iSup W = ⊤ ∧
      ∃ (i : Fin m → I) (g : ∀ k : Fin m, (W k).toScheme ⟶ (V (i k)).left),
        ∀ k : Fin m, g k ≫ (a (i k)).left = (W k).ι := by
  classical
  have hc : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (a i).left) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hcover
    exact hcover
  let E : PreZeroHypercover S :=
    ⟨I, fun i ↦ (V i).left, fun i ↦ (a i).left⟩
  have : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hc.1
  obtain ⟨n, b, U, hU, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let Y (k : Fin n) : Scheme.{u} := (U k).toScheme
  have (k : Fin n) : IsAffine (Y k) := hU k
  let p (k : Fin n) : Y k ⟶ S := (U k).ι ≫ (a (b k)).left
  have (k : Fin n) : WeaklyEtale ((a (b k)).left) := by
    exact (ofArrows_mem_precoverage_iff _).mp hc.2 |>.2 (b k)
  have (k : Fin n) : WeaklyEtale (p k) := inferInstance
  have : WeaklyEtale (Sigma.desc p) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ inferInstance
  have : Surjective (Sigma.desc p) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    simp only [TopologicalSpace.Opens.coe_top] at hcov
    convert hcov using 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨k, y, rfl⟩
      exact ⟨k, y.1, y.2, rfl⟩
    · rintro ⟨k, y, hy, rfl⟩
      exact ⟨k, ⟨y, hy⟩, rfl⟩
  let T : S.ProEt := ProEt.mk (Sigma.desc p)
  let q : T ⟶ ProEt.mk (𝟙 S) := MorphismProperty.Over.homMk (Sigma.desc p) (by
    change Sigma.desc p ≫ 𝟙 S = Sigma.desc p
    exact Category.comp_id _)
  have hq : Sieve.generate (Presieve.singleton q) ∈ ProEt.topology S (ProEt.mk (𝟙 S)) := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton (Sigma.desc p) ∈ proetalePrecoverage S
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (f := Sigma.desc p) inferInstance
  obtain ⟨s₀, hs₀⟩ := section_of_cover q hq hweak
  let s := s₀.left
  have hs : s ≫ Sigma.desc p = 𝟙 S := congrArg (fun g ↦ g.left) hs₀
  let O (k : Fin n) : S.Opens := s ⁻¹ᵁ (Sigma.ι Y k).opensRange
  have hdis : Pairwise (fun j k : Fin n ↦ Disjoint (O j) (O k)) := by
    intro j k hjk T hj hk x hx
    exact (disjoint_opensRange_sigmaι Y j k hjk).le_bot ⟨hj hx, hk hx⟩
  have hO : ∀ x : S, ∃ k, x ∈ O k := by
    intro x
    obtain ⟨k, y, hy⟩ := (sigmaOpenCover Y).exists_eq (s x)
    exact ⟨k, y, hy⟩
  have hclosed (k : Fin n) : IsClosed (O k : Set S) := by
    rw [← isOpen_compl_iff]
    have heq : (O k : Set S)ᶜ = ⋃ j : {j : Fin n // j ≠ k}, (O j.1 : Set _) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hO x
        exact ⟨⟨j, fun hjk ↦ hx (hjk ▸ hj)⟩, hj⟩
      · rintro ⟨j, hj⟩ hk
        exact (hdis j.2).le_bot ⟨hj, hk⟩
    rw [heq]
    exact isOpen_iUnion fun j ↦ (O j.1).isOpen
  have hfactor (k : Fin n) : Set.range ((O k).ι ≫ s).base ⊆
      Set.range (Sigma.ι Y k).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let t (k : Fin n) : (O k).toScheme ⟶ Y k :=
    IsOpenImmersion.lift (Sigma.ι Y k) ((O k).ι ≫ s) (hfactor k)
  have ht (k : Fin n) : t k ≫ p k = (O k).ι := by
    rw [← Sigma.ι_desc p k, ← Category.assoc, IsOpenImmersion.lift_fac,
      Category.assoc, hs, Category.comp_id]
  let K := {k : Fin n // (O k : Set S).Nonempty}
  let e : Fin (Nat.card K) ≃ K := (Finite.equivFin K).symm
  refine ⟨Nat.card K, fun k ↦ O (e k).1, fun k ↦ hclosed _, fun k ↦ (e k).2, ?_, ?_,
    fun k ↦ b (e k).1, fun k ↦ t (e k).1 ≫ (U (e k).1).ι, ?_⟩
  · intro j k hjk
    apply hdis
    intro h
    exact hjk (e.injective (Subtype.ext h))
  · apply top_unique
    intro x _
    obtain ⟨k, hk⟩ := hO x
    obtain ⟨j, hj⟩ := e.surjective ⟨k, x, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, by simpa only [hj] using hk⟩
  · intro k
    exact (Category.assoc _ _ _).trans (ht _)


end AlgebraicGeometry.Scheme
