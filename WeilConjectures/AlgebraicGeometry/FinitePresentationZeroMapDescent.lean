/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.Data.Finset.Order
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapAffineOpen

/-!
# Eventual vanishing of one finitely generated module map

## References

* Stacks Project, Limits, Tag 01ZR.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A map from a finite type quasi-coherent model to a finitely presented model
which vanishes on the inverse limit vanishes at some finite stage.
(Stacks, Tag 01ZR) -/
theorem finitePresentation_zero_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) [QuasiCompact f]
    (j : I) (hij : i ≤ j)
    (F G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map δ = 0) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (Over.homMk (Spec.map (R.map (homOfLE hjj')))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map δ = 0 := by
  classical
  let : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Xi.affineCover.finiteSubcover
  have one (a : 𝒰.I₀) := finitePresentation_zero_map_affine_open_eventually
    R c hc i f j hij F G hF_ft hF_qc hG_fp hG_qc δ hδ
    (𝒰.f a).opensRange (by
      exact isAffineOpen_opensRange (Xi.affineCover.f (Xi.affineCover.idx a.val)))
  choose stage hstage hzero using one
  let : Nonempty I := ⟨j⟩
  obtain ⟨l, hl⟩ := (insert j (Finset.univ.image stage)).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  refine ⟨l, hjl, ?_⟩
  let p := pullback.fst f (Spec.map (R.map (homOfLE (hij.trans hjl))))
  let d := (Scheme.Modules.moduleBaseChange f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map δ
  have hz (a : 𝒰.I₀) (W) (hW : W ≤ p ⁻¹ᵁ (𝒰.f a).opensRange) : d.app W = 0 := by
    apply hzero a l hjl _ W hW
    exact hl (stage a)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change d.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, (Scheme.Modules.isSheaf _)⟩
    (fun a : 𝒰.I₀ ↦ W ⊓ p ⁻¹ᵁ (𝒰.f a).opensRange) W
    (fun _ ↦ homOfLE inf_le_left) ?_ (d.app W s) 0 ?_
  · intro x hx
    obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (p x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, hx, ⟨y, hy⟩⟩
  · intro a
    have hn := congrArg (fun q ↦ q s)
      (d.mapPresheaf.naturality (homOfLE
        (inf_le_left : W ⊓ p ⁻¹ᵁ (𝒰.f a).opensRange ≤ W)).op)
    rw [Scheme.Modules.mapPresheaf_app, hz a _ inf_le_right] at hn
    simpa using hn.symm

end AlgebraicGeometry
