/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Data.Finset.Order
import WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapDescent

/-!
# Descent of finite relations among module maps

## References

* Stacks Project, Limits, Tag 01ZR.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem moduleBaseChange_additive {X S : Scheme.{u}} (f : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) :
    (Scheme.Modules.moduleBaseChange f g).Additive := by
  exact (Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction
    (baseChangeMap f g))).left_adjoint_additive

private theorem moduleBaseChange_map_eq_comp {X S : Scheme.{u}} (f : X ⟶ S)
    {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T')
    {F G : (pullback f T.hom).Modules} (a b : F ⟶ G)
    (hab : (Scheme.Modules.moduleBaseChange f g).map a =
      (Scheme.Modules.moduleBaseChange f g).map b) :
    (Scheme.Modules.moduleBaseChange f (h ≫ g)).map a =
      (Scheme.Modules.moduleBaseChange f (h ≫ g)).map b := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (baseChangeMap f h) (baseChangeMap f g)
  have e' : Scheme.Modules.moduleBaseChange f (h ≫ g) ≅
      Scheme.Modules.moduleBaseChange f g ⋙ Scheme.Modules.moduleBaseChange f h := by
    simpa only [Scheme.Modules.moduleBaseChange, baseChangeMap_comp] using e
  apply (cancel_mono (e'.hom.app G)).1
  rw [e'.hom.naturality, e'.hom.naturality]
  exact congrArg (fun t ↦ e'.hom.app F ≫ (Scheme.Modules.moduleBaseChange f h).map t) hab

/-- Finite relations between descended module maps hold at a later stage.
(Stacks, Tag 01ZR)

The modules are the given models on `X_j`; the modules on `X` are their canonical
base changes. The finite type `M` indexes the finite collection of modules (`[Finite M]`). -/
theorem finiteRelation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : Type u) [Finite M]
    (Fj : M → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hFj_fp : ∀ k : M, (Fj k).IsFinitePresentation)
    (hFj_qc : ∀ k : M, (Fj k).IsQuasicoherent)
    (n : ℕ) (src tgt : Fin n → M)
    (lhs rhs : ∀ k : Fin n, Fj (src k) ⟶ Fj (tgt k))
    (hrel : ∀ k : Fin n,
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (lhs k) =
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (rhs k)) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      ∀ k : Fin n,
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (lhs k) =
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (rhs k) := by
  classical
  let toLimit := Scheme.Modules.moduleBaseChange f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
  let : toLimit.Additive := moduleBaseChange_additive f _
  have one (k : Fin n) : ∃ (l : I) (hjl : j ≤ l),
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjl)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (lhs k) =
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjl)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (rhs k) := by
    let := hFj_fp (src k)
    have hz : toLimit.map (lhs k - rhs k) = 0 := by
      rw [Functor.map_sub, hrel k, sub_self]
    obtain ⟨l, hjl, hl⟩ := finitePresentation_zero_map_descent R c hc i f j hij
      (Fj (src k)) (Fj (tgt k)) (by infer_instance) (hFj_qc (src k))
      (hFj_fp (tgt k)) (hFj_qc (tgt k)) (lhs k - rhs k) hz
    let toStage := Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
      (Over.homMk (Spec.map (R.map (homOfLE hjl)))
        (show Spec.map (R.map (homOfLE hjl)) ≫
          Spec.map (R.map (homOfLE hij)) =
          Spec.map (R.map (homOfLE (hij.trans hjl))) by
            rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let : toStage.Additive := moduleBaseChange_additive f _
    exact ⟨l, hjl, sub_eq_zero.mp (by simpa only [Functor.map_sub] using hl)⟩
  choose stage hstage hmap using one
  let : Nonempty I := ⟨j⟩
  obtain ⟨l, hl⟩ := (insert j (Finset.univ.image stage)).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  refine ⟨l, hjl, ?_⟩
  intro k
  have hkl : stage k ≤ l := hl (stage k)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩))
  let g : Over.mk (Spec.map (R.map (homOfLE (hij.trans (hstage k))))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE (hstage k))))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let h : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans (hstage k))))) :=
    Over.homMk (Spec.map (R.map (homOfLE hkl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  have he : h ≫ g = Over.homMk (Spec.map (R.map (homOfLE hjl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl) := by
    ext
    change Spec.map (R.map (homOfLE hkl)) ≫
      Spec.map (R.map (homOfLE (hstage k))) = Spec.map (R.map (homOfLE hjl))
    rw [← Spec.map_comp, ← R.map_comp]
    rfl
  have hh := moduleBaseChange_map_eq_comp f g h (lhs k) (rhs k) (hmap k)
  rw [he] at hh
  exact hh

end AlgebraicGeometry
