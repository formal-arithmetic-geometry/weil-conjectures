/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Finite affine refinements of pro-etale covers

Source: Stacks Project, proetale.tex, Tags 0989, 098A and 098C.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t i
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A pro-etale cover of a nonempty quasi-compact scheme has a finite nonempty
refinement by affine opens in its members. Source: Stacks Project, proetale.tex,
Tags 0989, 098A and 098C. Take a finite affine open cover of the base; on each member
use the finite affine refinement in the quasi-compact covering condition. The latter
is a cover because its target and sources are affine. Compose these covers with the
base open cover. The resulting maps into the original members are open immersions;
replace their affine sources by their open images and reindex the finite family by
Fin n. Joint surjectivity and nonemptiness of the base imply n > 0.
(blueprint: lem-sfb-finite-affine-cover-refinement-general). -/
theorem finite_affine_proetale_refinement (S : Scheme.{t}) [Nonempty S] [CompactSpace S]
    (I : Type i) (U : I → S.ProEt)
    (hcover : Presieve.ofArrows (fun k ↦ (U k).left) (fun k ↦ (U k).hom) ∈
      proetalePrecoverage.coverings S) :
    ∃ (n : ℕ) (_hn : 0 < n) (α : Fin n → I) (V : ∀ j, (U (α j)).left.Opens),
      (∀ j, IsAffineOpen (V j)) ∧
      Presieve.ofArrows (fun j ↦ (V j).toScheme)
        (fun j ↦ (V j).ι ≫ (U (α j)).hom) ∈ proetalePrecoverage.coverings S := by
  classical
  let E : S.Cover (propQCPrecoverage @WeaklyEtale) :=
    { I₀ := I, X k := (U k).left, f k := (U k).hom, mem₀ := hcover }
  let A := S.affineCover.finiteSubcover
  have hA (k : A.I₀) : IsAffine (A.X k) := inferInstance
  have hex (k : A.I₀) :=
    QuasiCompactCover.exists_hom (Cover.forgetQc (E.pullback₁ (A.f k)))
  choose T f hfin hopen using hex
  have (k : A.I₀) : Finite (T k).I₀ := hfin k
  have (k : A.I₀) (j : (T k).I₀) : IsOpenImmersion ((f k).h₀ j) := hopen k j
  let H (k : A.I₀) : (A.X k).Cover proetalePrecoverage :=
    Cover.ofQuasiCompactCover (T k).cover
  let A' : S.Cover proetalePrecoverage :=
    A.weaken zariskiPrecoverage_le_propQCPrecoverage
  let D := A'.bind H
  let α (j : D.I₀) : I := (f j.1).s₀ j.2
  let g (j : D.I₀) : D.X j ⟶ (U (α j)).left :=
    (f j.1).h₀ j.2 ≫ pullback.snd (A.f j.1) (E.f (α j))
  have hg (j : D.I₀) : IsOpenImmersion (g j) := by dsimp [g]; infer_instance
  have hw (j : D.I₀) : g j ≫ (U (α j)).hom = D.f j := by
    dsimp [g, D, H, A', α]
    have hf := (f j.1).w₀ j.2
    change (f j.1).h₀ j.2 ≫ pullback.fst (A.f j.1) (E.f ((f j.1).s₀ j.2)) =
      (T j.1).cover.f j.2 at hf
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hf]
    rfl
  have hDX (j : D.I₀) : IsAffine (D.X j) := by
    change IsAffine (Spec ((T j.1).X j.2))
    infer_instance
  have hga (j : D.I₀) : IsAffineOpen (g j).opensRange := isAffineOpen_opensRange _
  let D' : S.Cover proetalePrecoverage :=
    { I₀ := D.I₀
      X j := (g j).opensRange.toScheme
      f j := (g j).opensRange.ι ≫ (U (α j)).hom
      mem₀ := by
        let D₀ : PreZeroHypercover S :=
          { I₀ := D.I₀
            X j := (g j).opensRange.toScheme
            f j := (g j).opensRange.ι ≫ (U (α j)).hom }
        let e : D.toPreZeroHypercover ≅ D₀ :=
          PreZeroHypercover.isoMk (Equiv.refl _) (fun j ↦ (g j).isoOpensRange)
            (fun j ↦ by
              change (g j).isoOpensRange.hom ≫
                ((g j).opensRange.ι ≫ (U (α j)).hom) = D.f j
              rw [Hom.isoOpensRange_hom_ι_assoc, hw])
        exact PreZeroHypercover.presieve₀_mem_of_iso e D.mem₀ }
  have : Finite D'.I₀ := by
    change Finite (Σ k : A.I₀, (T k).I₀)
    infer_instance
  have : Fintype D'.I₀ := Fintype.ofFinite _
  let e := Fintype.equivFin D'.I₀
  have hnon : Nonempty D'.I₀ := ⟨Scheme.Cover.idx
    (Cover.forgetQc D')
    (Classical.choice inferInstance)⟩
  have hpos : 0 < Fintype.card D'.I₀ := Fintype.card_pos
  refine ⟨_, hpos, fun j ↦ α (e.symm j), fun j ↦ (g (e.symm j)).opensRange,
    fun j ↦ hga _, ?_⟩
  exact (D'.reindex e.symm).mem₀

end AlgebraicGeometry.Scheme
