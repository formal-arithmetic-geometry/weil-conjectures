/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverLocalLifts

/-!
# Refinements of finite split étale hypercovers

Blueprint `lem-weil-pbc-hypercover-refinement`: finite split étale hypercovers of a
quasi-compact quasi-separated scheme exist, any two have a common refinement, parallel
refinements become homotopic after refinement, finitely many local lifting requirements can be
solved after refinement, and semi-representable hypercovers are refined through any finite
degree. The constructions use `AlgebraicGeometry.FiniteSplitHypercoverEngine.exists_hypercover`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

lemma _root_.CategoryTheory.GrothendieckTopology.iInf_mem_of_finite {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {T : C} {ι : Type*} [Finite ι] (s : ι → Sieve T)
    (h : ∀ i, s i ∈ J T) : ⨅ i, s i ∈ J T := by
  have := Fintype.ofFinite ι
  rw [← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using J.top_mem T
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (h a) ih

/-- A coproduct of coproducts is a coproduct. -/
def _root_.CategoryTheory.Limits.isColimitCofanSigma {C : Type*} [Category* C] {I : Type*}
    {J : I → Type*} {P : (Σ i, J i) → C} {N : I → C} (ιN : ∀ a : Σ i, J i, P a ⟶ N a.1)
    (hN : ∀ i, IsColimit (Cofan.mk (N i) fun j : J i ↦ ιN ⟨i, j⟩)) {Z : C} (c : ∀ i, N i ⟶ Z)
    (hc : IsColimit (Cofan.mk Z c)) : IsColimit (Cofan.mk Z fun a ↦ ιN a ≫ c a.1) :=
  Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hc fun i ↦ Cofan.IsColimit.desc (hN i) fun j ↦ t.inj ⟨i, j⟩)
    (fun t a ↦ by
      obtain ⟨i, j⟩ := a
      simp only [cofan_mk_inj, Category.assoc]
      rw [Cofan.IsColimit.fac hc (fun i ↦ _) i]
      exact Cofan.IsColimit.fac (hN i) (fun j ↦ t.inj ⟨i, j⟩) j)
    (fun t m hm ↦ by
      refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
      refine Cofan.IsColimit.hom_ext (hN i) _ _ fun j ↦ ?_
      simp only [cofan_mk_inj] at hm ⊢
      rw [← Category.assoc, hm ⟨i, j⟩, Cofan.IsColimit.fac hc (fun i ↦ _) i]
      exact (Cofan.IsColimit.fac (hN i) (fun j ↦ t.inj ⟨i, j⟩) j).symm)

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

open Scheme.Etale in
/-- Blueprint `lem-weil-pbc-hypercover-refinement`: finite split étale hypercovers exist. -/
theorem nonempty (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (FiniteSplitEtaleHypercover X) := by
  obtain ⟨V, -, -⟩ := FiniteSplitHypercoverEngine.exists_hypercover
    hasLocalLifts_const_terminal (fun _ ↦ ⊤) (fun m ↦ X.smallEtaleTopology.top_mem _)
  exact ⟨V⟩

open Scheme.Etale in
/-- Blueprint `lem-weil-pbc-hypercover-refinement`: two finite split étale hypercovers have a
common refinement. -/
theorem exists_common_refinement (U V : FiniteSplitEtaleHypercover X) :
    ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧ Nonempty (W.Refinement V) := by
  obtain ⟨W, ℓ, -⟩ := FiniteSplitHypercoverEngine.exists_hypercover
    (hasLocalLifts_prod U.hasLocalLifts V.hasLocalLifts) (fun _ ↦ ⊤)
    (fun m ↦ X.smallEtaleTopology.top_mem _)
  exact ⟨W, ⟨ℓ ≫ prodSimplicialFst _ _⟩, ⟨ℓ ≫ prodSimplicialSnd _ _⟩⟩

/-- Blueprint `lem-weil-pbc-hypercover-refinement`: parallel refinements become homotopic after
refinement. -/
theorem exists_homotopic_refinement (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V) :
    ∃ (W : FiniteSplitEtaleHypercover X) (c : W.Refinement U),
      isRefinementHomotopic (c ≫ a) (c ≫ b) := by
  sorry

/-- Blueprint `lem-weil-pbc-hypercover-refinement`: finite split étale hypercovers exist, and
their homotopy category is cofiltered. -/
theorem exists_and_cofiltered (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (FiniteSplitEtaleHypercover X) ∧
      (∀ U V : FiniteSplitEtaleHypercover X,
        ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧
          Nonempty (W.Refinement V)) ∧
      (∀ (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V),
        ∃ (W : FiniteSplitEtaleHypercover X) (c : W.Refinement U),
          isRefinementHomotopic (c ≫ a) (c ≫ b)) :=
  ⟨nonempty X, exists_common_refinement, exists_homotopic_refinement⟩

/-- Blueprint `lem-weil-pbc-hypercover-refinement`: finitely many local lifting requirements on
the terms of a finite split étale hypercover in finitely many degrees are solved by a
refinement. -/
theorem exists_refinement_solving_local_requirements
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : FiniteSplitEtaleHypercover X) (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (R : ∀ j : Fin k, Sieve (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))
    (hR : ∀ j, R j ∈ X.smallEtaleTopology
      (U.simplicial.obj (op (SimplexCategory.mk (degree j).val)))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ n : Fin (r + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n.val))),
        Nonempty (IsColimit (Cofan.mk (V.simplicial.obj (op (SimplexCategory.mk n.val))) ι)) ∧
          ∀ (j : Fin k) (h : degree j = n) (i : Fin l),
            R j (ι i ≫ f.app (op (SimplexCategory.mk n.val)) ≫
              eqToHom (congrArg (fun m : Fin (r + 1) ↦
                U.simplicial.obj (op (SimplexCategory.mk m.val))) h.symm)) := by
  classical
  let S : ∀ m : ℕ, Sieve (U.simplicial _⦋m⦌) := fun m ↦
    ⨅ x : Σ j : Fin k, (⦋(degree x.1).val⦌ ⟶ ⦋m⦌), (R x.1).pullback (U.simplicial.map x.2.op)
  sorry

/-- Blueprint `lem-weil-pbc-hypercover-refinement`: a semi-representable hypercover is refined,
through any finite degree, by a finite split étale hypercover. -/
theorem exists_truncated_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover
      (K ⋙ FormalCoproduct.incl.{u} X.Etale)) (r : ℕ) :
    ∃ V : FiniteSplitEtaleHypercover X,
      Nonempty ((SimplicialObject.truncation r).obj V.simplicial ⟶
          (SimplicialObject.truncation r).obj K) := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover
