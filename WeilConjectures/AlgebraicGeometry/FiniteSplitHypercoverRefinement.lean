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
  classical
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
      have e := Cofan.IsColimit.fac hc
        (fun i ↦ Cofan.IsColimit.desc (hN i) fun j ↦ t.inj ⟨i, j⟩) i
      have e' := Cofan.IsColimit.fac (hN i) (fun j ↦ t.inj ⟨i, j⟩) j
      simp only [cofan_mk_inj] at e e' ⊢
      rw [Category.assoc, e, e'])
    (fun t m hm ↦ by
      refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
      refine Cofan.IsColimit.hom_ext (hN i) _ _ fun j ↦ ?_
      have e := Cofan.IsColimit.fac hc
        (fun i ↦ Cofan.IsColimit.desc (hN i) fun j ↦ t.inj ⟨i, j⟩) i
      have e' := Cofan.IsColimit.fac (hN i) (fun j ↦ t.inj ⟨i, j⟩) j
      simp only [cofan_mk_inj] at hm e e' ⊢
      rw [← Category.assoc, hm ⟨i, j⟩, e, e'])

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
    ⨅ x : Σ j : Fin k, (⦋(degree j).val⦌ ⟶ ⦋m⦌), (R x.1).pullback (U.simplicial.map x.2.op)
  have hS : ∀ m, S m ∈ X.smallEtaleTopology (U.simplicial _⦋m⦌) := fun m ↦
    X.smallEtaleTopology.iInf_mem_of_finite _ fun x ↦
      X.smallEtaleTopology.pullback_stable _ (hR x.1)
  obtain ⟨V, ℓ, hV⟩ := FiniteSplitHypercoverEngine.exists_hypercover
    U.toSplitEtaleHypercover.hasLocalLifts S hS
  choose kk P ιP hP hgood using hV
  refine ⟨V, ℓ, fun n ↦ ?_⟩
  let I := Σ A : SimplicialObject.Splitting.IndexSet (op ⦋n.val⦌), Fin (kk A.1.unop.len)
  let e := (Fintype.equivFin I).symm
  have hcol : IsColimit (Cofan.mk (V.simplicial.obj (op ⦋n.val⦌))
      fun a : I ↦ ιP _ a.2 ≫ (V.splitting.cofan (op ⦋n.val⦌)).inj a.1) :=
    isColimitCofanSigma (fun a : I ↦ ιP _ a.2) (fun A ↦ (hP _).some) _
      (V.splitting.isColimit (op ⦋n.val⦌))
  refine ⟨Fintype.card I, fun i ↦ P _ (e i).2,
    fun i ↦ ιP _ (e i).2 ≫ (V.splitting.cofan (op ⦋n.val⦌)).inj (e i).1,
    ⟨Cofan.isColimitEquivOfEquiv e _ hcol⟩, fun j h i ↦ ?_⟩
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  obtain ⟨A, i'⟩ := e i
  rw [SimplicialObject.Splitting.cofan_inj_eq]
  dsimp only
  rw [Category.assoc, Category.assoc, ℓ.naturality, ← Category.assoc, ← Category.assoc]
  have hmem := hgood _ i'
  have hle : S A.1.unop.len ≤ (R j).pullback (U.simplicial.map A.e.op) :=
    iInf_le (fun x : Σ j : Fin k, (⦋(degree j).val⦌ ⟶ ⦋A.1.unop.len⦌) ↦
      (R x.1).pullback (U.simplicial.map x.2.op)) ⟨j, A.e⟩
  exact hle _ (by simpa [Category.assoc] using hmem)

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
