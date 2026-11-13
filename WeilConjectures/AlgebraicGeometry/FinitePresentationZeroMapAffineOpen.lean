/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest
import WeilConjectures.AlgebraicGeometry.FinitePresentationSectionAffineOpenVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Data.Finset.Order

/-!
# Eventual vanishing on one affine open

## References

* Stacks Project, Limits, Tag 01ZR; Algebra, Tag 05N7.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry


/-- Vanishing on one affine open of the fixed model holds at every sufficiently late stage.
No quasi-compactness of the whole model is needed.
(Stacks, Tag 01ZR, Tag 05N7) -/
theorem finitePresentation_zero_map_affine_open_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (F G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map δ = 0)
    (U : Xi.Opens) (hU : IsAffineOpen U) :
    ∃ (l : I), j ≤ l ∧ ∀ (k : I) (hjk : j ≤ k), l ≤ k →
      ∀ (W : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjk))))).Opens),
        W ≤ (pullback.fst f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))) ⁻¹ᵁ U →
        ((Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map δ).app W = 0 := by
  classical
  let V := (pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U
  have : IsAffineHom (pullback.fst f (Spec.map (R.map (homOfLE hij)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hV : IsAffineOpen V := hU.preimage _
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_affine_finiteType_pullback_zero_test
    F hF_ft hF_qc V hV
  let a : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  let g := baseChangeMap f a
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  have hy (x : Γ(F, V)) : (adj.unit.app G).val.app (op V) (δ.app V x) = 0 := by
    have hn := adj.unit_naturality δ
    rw [show (Scheme.Modules.tensorPullback g).map δ = 0 from hδ,
      Functor.map_zero, comp_zero] at hn
    have hx := congrArg (fun t => t.val.app (op V) x) hn.symm
    exact hx
  let adjstage (k : I) (hjk : j ≤ k) := Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))))
  have hx (x : s) := finitePresentation_section_affine_open_eventually_zero
    R c hc i f j hij G hG_fp hG_qc U hU (δ.app V x.1) adj adjstage (hy x.1)
  choose l hl hzero using hx
  let : Nonempty I := ⟨j⟩
  obtain ⟨b, hb⟩ := (s.attach.image l).exists_le
  obtain ⟨L, hjL, hbL⟩ := exists_ge_ge j b
  refine ⟨L, hjL, ?_⟩
  intro k hjk hLk W hW
  let ak : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let gk := baseChangeMap f ak
  apply hs G hG_qc δ _ gk ?_ W ?_
  · intro x hx
    exact hzero ⟨x, hx⟩ k hjk
      ((hb _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)).trans
        (hbL.trans hLk))
  · change W ≤ gk ⁻¹ᵁ ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage]
    simpa [gk, baseChangeMap] using hW

end AlgebraicGeometry
