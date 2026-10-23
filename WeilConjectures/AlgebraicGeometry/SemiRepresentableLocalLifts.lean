/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverEngine
public import WeilConjectures.CategoryTheory.SimplicialBoundaryFaces

/-!
# Semi-representable hypercovers have local lifts

If a simplicial object `K` of `X_ét` is a semi-representable hypercover (its matching maps,
computed among formal coproducts, are coverings), then every boundary of a simplex of `K`
lifts étale locally to a simplex of `K`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial CategoryTheory.SimplicialObject

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A boundary cone is determined by its values on the codimension one faces. -/
lemma _root_.CategoryTheory.SimplicialObject.BoundaryCone.ext_of_δ {C : Type*} [Category* C]
    {W : SimplicialObject C} {n : ℕ} {N : C} {c d : BoundaryCone W (n + 1) N}
    (h : ∀ i : Fin (n + 2), c.π ⦋n⦌ (by simp) (SimplexCategory.δ i) =
      d.π ⦋n⦌ (by simp) (SimplexCategory.δ i)) : c = d := by
  refine BoundaryCone.ext' fun Δ hΔ θ ↦ ?_
  obtain ⟨i, θ', rfl⟩ := SimplexCategory.exists_eq_comp_δ_of_len_lt hΔ θ
  rw [← c.w _ _ (by simp) hΔ θ', ← d.w _ _ (by simp) hΔ θ', h]

open FormalCoproduct in
lemma liftSieve_mem_of_isSemiRepresentableCovering (K : SimplicialObject X.Etale) (m : ℕ)
    {T : X.Etale} (p : BoundaryCone K m T)
    (ψ : (incl.{u} X.Etale).obj T ⟶ semiRepresentableMatchingObject (K ⋙ incl.{u} X.Etale) m)
    (hψ : ∀ {T' : X.Etale} (g : T' ⟶ T) (h : T' ⟶ K _⦋m⦌),
      (incl.{u} X.Etale).map h ≫ semiRepresentableMatchingMap (K ⋙ incl.{u} X.Etale) m =
        (incl.{u} X.Etale).map g ≫ ψ → BoundaryCone.ofSimplex h = p.precomp g)
    (hcov : IsSemiRepresentableCovering
      (semiRepresentableMatchingMap (K ⋙ incl.{u} X.Etale) m)) :
    Etale.liftSieve p ∈ X.smallEtaleTopology T := by
  refine X.smallEtaleTopology.superset_covering ?_
    (X.smallEtaleTopology.pullback_stable (ψ.φ PUnit.unit) (hcov (ψ.f PUnit.unit)))
  rintro T' g ⟨Y, h, _, ⟨i⟩, hfac⟩
  obtain ⟨⟨⟩, hi⟩ := i
  refine ⟨h, hψ g h ?_⟩
  refine FormalCoproduct.hom_ext (funext fun _ ↦ hi) fun _ ↦ ?_
  exact (Category.assoc _ _ _).trans hfac

open FormalCoproduct in
/-- A semi-representable hypercover has local lifts. -/
lemma hasLocalLifts_of_isSemiRepresentableHypercover (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover (K ⋙ incl.{u} X.Etale)) : Etale.HasLocalLifts K := by
  intro m T p
  match m, p with
  | 0, p =>
    refine liftSieve_mem_of_isSemiRepresentableCovering K 0 p
      ((isTerminalIncl (Etale.mk (𝟙 X)) ((Over.mkIdTerminal (X := X)).isTerminalOfObj
        (Etale.forget X) (Etale.mk (𝟙 X)))).from _) (fun g h _ ↦ ?_) (hK 0)
    exact BoundaryCone.ext' fun Δ hΔ _ ↦ absurd hΔ (Nat.not_lt_zero _)
  | 1, p =>
    refine liftSieve_mem_of_isSemiRepresentableCovering K 1 p
      (Pi.lift fun i : Fin 2 ↦ (incl.{u} X.Etale).map (p.π ⦋0⦌ (by simp) (SimplexCategory.δ i)))
      (fun g h hgh ↦ ?_) (hK 1)
    refine BoundaryCone.ext_of_δ fun i ↦ ?_
    have := congrArg (· ≫ Pi.π _ i) hgh
    simp only [semiRepresentableMatchingMap, Category.assoc, limit.lift_π, Fan.mk_pt,
      Fan.mk_π_app] at this
    exact (incl.{u} X.Etale).map_injective
      (by simpa [SimplicialObject.δ, ← Functor.map_comp] using this)
  | n + 2, p =>
    refine liftSieve_mem_of_isSemiRepresentableCovering K (n + 2) p
      (Multiequalizer.lift (SimplicialObject.matchingBoundaryIndex (K ⋙ incl.{u} X.Etale) n) _
        (fun i : Fin (n + 3) ↦
          (incl.{u} X.Etale).map (p.π ⦋n + 1⦌ (by simp) (SimplexCategory.δ i)))
        (by
          rintro ⟨⟨a, b⟩, hab⟩
          change (incl.{u} X.Etale).map (p.π ⦋n + 1⦌ (by simp) (SimplexCategory.δ a)) ≫
              (incl.{u} X.Etale).map (K.δ (b.pred (Fin.ne_zero_of_lt hab))) =
            (incl.{u} X.Etale).map (p.π ⦋n + 1⦌ (by simp) (SimplexCategory.δ b)) ≫
              (incl.{u} X.Etale).map (K.δ (a.castLT
                (Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt))))
          rw [← Functor.map_comp, ← Functor.map_comp]
          congr 1
          have hb : b = (b.pred (Fin.ne_zero_of_lt hab)).succ := (Fin.succ_pred _ _).symm
          have H : a.castLT (Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)) ≤
              b.pred (Fin.ne_zero_of_lt hab) := by
            rw [Fin.le_iff_val_le_val]
            have h' : a.val < b.val := hab
            simp only [Fin.val_castLT, Fin.val_pred]
            omega
          rw [SimplicialObject.δ, SimplicialObject.δ, p.w _ _ (by simp) (by simp),
            p.w _ _ (by simp) (by simp)]
          congr 1
          have := SimplexCategory.δ_comp_δ H
          rw [← hb] at this
          exact this.symm))
      (fun g h hgh ↦ ?_) (hK (n + 2))
    refine BoundaryCone.ext_of_δ fun i ↦ ?_
    have := congrArg (· ≫ Multiequalizer.ι _ i) hgh
    simp only [semiRepresentableMatchingMap, Category.assoc, Multiequalizer.lift_ι] at this
    exact (incl.{u} X.Etale).map_injective
      (by simpa [SimplicialObject.δ, ← Functor.map_comp] using this)

end AlgebraicGeometry.Scheme
