/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Clopen partitions refining coverings of w-contractible affine schemes

Source: blueprint, sec-proetale-coefficients, sk-thm-pe-weakly-contractible-basis,
node det-pe-wcb-clopen-partition; Stacks Project, Tag 098F, implication (1) to (2)
(blueprint: det-pe-wcb-clopen-partition).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A covering of a w-contractible affine object of the small pro-étale site admits a
finite partition into clopen open subschemes, each mapping over the affine target to a
selected covering member. The partition has no pieces when the target is empty.

Source: blueprint node det-pe-wcb-clopen-partition; Stacks Project, Tag 098F,
implication (1) to (2) (blueprint: det-pe-wcb-clopen-partition).

Proof:
1. For the empty target take the empty partition. Otherwise sk-def-pe-site and
   def-weil-pbc-proetale-covering give finitely many affine opens in covering members
   whose images cover the affine target. The base change along the identity of the
   target identifies these with affine opens in the original members. All covering
   arrows are weakly étale; the original index set need not be finite.
2. Form their disjoint union, using lem-weil-pbc-scheme-coproduct-family. Its components
   are clopen and disjoint. It is affine by lem-weil-pbc-affine-morphism-permanence,
   clause (4), and its map to the target is surjective since the component images cover.
3. The inclusions of the affine opens are étale by lem-weil-pbc-open-immersion-etale,
   hence weakly étale by det-pe-morphisms-etale-comparison, clause (1). Composition and
   Zariski source locality from sk-lem-pe-weakly-etale-stability make the disjoint-union
   map weakly étale. Clause (4) of det-pe-morphisms-etale-comparison gives flatness of
   its ring map and multiplication. Surjectivity and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat give faithful flatness.
4. Apply det-pe-wcb-split-cover to obtain a section of this faithfully flat weakly
   étale affine map, using w-contractibility of the target ring.
5. Pull the clopen components back along this section. Their inverse images are clopen,
   disjoint and cover the target. Restrict the section to each inverse image and then
   compose with the inclusion into its chosen covering member. The section equation
   says that the resulting map is over the target. Discard empty pieces and reindex
   the remaining finite family by `Fin m`.
-/
theorem proetale_wContractible_clopen_partition
    (X : Scheme.{u}) (D : Type u) [CommRing D] [IsWContractibleRing D]
    (f : Spec (.of D) ⟶ X) [WeaklyEtale f]
    (I : Type v) (V : I → X.ProEt) (a : ∀ i : I, V i ⟶ ProEt.mk f)
    (hcover : Presieve.ofArrows V a ∈ ProEt.precoverage X (ProEt.mk f)) :
    ∃ (m : ℕ) (W : Fin m → (Spec (.of D)).Opens),
      (∀ k : Fin m, IsClosed (W k : Set (Spec (.of D)))) ∧
      (∀ k : Fin m, (W k : Set (Spec (.of D))).Nonempty) ∧
      Pairwise (fun j k : Fin m ↦ Disjoint (W j) (W k)) ∧
      iSup W = ⊤ ∧
      ∃ (i : Fin m → I) (g : ∀ k : Fin m, (W k).toScheme ⟶ (V (i k)).left),
        ∀ k : Fin m, g k ≫ (a (i k)).left = (W k).ι := by
  classical
  have hc : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (a i).left) ∈
      proetalePrecoverage (Spec (.of D)) := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hcover
    exact hcover
  let E : PreZeroHypercover (Spec (.of D)) :=
    ⟨I, fun i ↦ (V i).left, fun i ↦ (a i).left⟩
  have : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hc.1
  obtain ⟨n, b, U, hU, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let Y (k : Fin n) : Scheme.{u} := (U k).toScheme
  have (k : Fin n) : IsAffine (Y k) := hU k
  let p (k : Fin n) : Y k ⟶ Spec (.of D) := (U k).ι ≫ (a (b k)).left
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
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (Sigma.desc p)
  let O (k : Fin n) : (Spec (.of D)).Opens := s ⁻¹ᵁ (Sigma.ι Y k).opensRange
  have hdis : Pairwise (fun j k : Fin n ↦ Disjoint (O j) (O k)) := by
    intro j k hjk T hj hk x hx
    exact (disjoint_opensRange_sigmaι Y j k hjk).le_bot ⟨hj hx, hk hx⟩
  have hO : ∀ x : Spec (.of D), ∃ k, x ∈ O k := by
    intro x
    obtain ⟨k, y, hy⟩ := (sigmaOpenCover Y).exists_eq (s x)
    exact ⟨k, y, hy⟩
  have hclosed (k : Fin n) : IsClosed (O k : Set (Spec (.of D))) := by
    rw [← isOpen_compl_iff]
    have heq : (O k : Set (Spec (.of D)))ᶜ = ⋃ j : {j : Fin n // j ≠ k}, (O j.1 : Set _) := by
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
  let K := {k : Fin n // (O k : Set (Spec (.of D))).Nonempty}
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
