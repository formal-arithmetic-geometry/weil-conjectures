/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Data.Fintype.Order

/-!
# Simultaneous descent of a finite family of scheme morphisms

## References

* Stacks Project, Limits, Tag 01ZM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Finitely many morphisms from pullbacks along the limit projection to a scheme of finite
presentation over stage `i` descend simultaneously to a single later stage
(Stacks, Tag 01ZM (2)). -/
theorem finite_pullback_hom_descent
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i : I) (n : ℕ)
    (V : Fin n → Scheme.{u}) (W : Scheme.{u})
    (pV : ∀ a, V a ⟶ D.obj (op i)) (pW : W ⟶ D.obj (op i))
    [∀ a, LocallyOfFinitePresentation (pV a)] [∀ a, QuasiCompact (pV a)]
    [∀ a, QuasiSeparated (pV a)]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW]
    (ψ : ∀ a, pullback (pV a) (c.π.app (op i)) ⟶ W)
    (hψ : ∀ a, ψ a ≫ pW = pullback.fst (pV a) (c.π.app (op i)) ≫ pV a) :
    ∃ (j : I) (h : i ≤ j)
      (ψj : ∀ a, pullback (pV a) (D.map (homOfLE h).op) ⟶ W),
      (∀ a, ψj a ≫ pW = pullback.fst (pV a) (D.map (homOfLE h).op) ≫ pV a) ∧
      ∀ a,
        pullback.map (pV a) (c.π.app (op i)) (pV a) (D.map (homOfLE h).op)
          (𝟙 _) (c.π.app (op j)) (𝟙 _) (by simp) (by simp) ≫ ψj a = ψ a  := by
  classical
  have hex (a : Fin n) := Scheme.exists_pullback_hom_of_isLimit hc (pV a) pW (ψ a) (hψ a)
  choose k b θ hθ heq using hex
  obtain ⟨l, hl⟩ := Finite.bddAbove_range (fun a ↦ (k a).unop)
  obtain ⟨j, hij, hlj⟩ := exists_ge_ge i l
  have hkj (a : Fin n) : (k a).unop ≤ j := le_trans (hl ⟨a, rfl⟩) hlj
  let m (a : Fin n) : op j ⟶ k a := (homOfLE (hkj a)).op
  have hf (a : Fin n) : D.map (homOfLE hij).op = D.map (m a) ≫ D.map (b a) := by
    rw [← D.map_comp]
    congr 1
  let M (a : Fin n) := pullback.map (pV a) (D.map (homOfLE hij).op)
    (pV a) (D.map (b a)) (𝟙 _) (D.map (m a)) (𝟙 _) (by simp) (by simp [hf a])
  refine ⟨j, hij, (fun a ↦ M a ≫ θ a), ?_, ?_⟩
  · intro a
    simp only [Category.assoc, hθ a]
    dsimp [M]
    simp
  · intro a
    have hm : pullback.map (pV a) (c.π.app (op i)) (pV a)
        (D.map (homOfLE hij).op) (𝟙 _) (c.π.app (op j)) (𝟙 _)
        (by simp) (by simp) ≫ M a =
        pullback.map (pV a) (c.π.app (op i)) (pV a) (D.map (b a))
          (𝟙 _) (c.π.app (k a)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext
      · simp [M]
      · simp [M, c.w (m a)]
    rw [← Category.assoc, hm]
    exact heq a


end AlgebraicGeometry.Scheme
