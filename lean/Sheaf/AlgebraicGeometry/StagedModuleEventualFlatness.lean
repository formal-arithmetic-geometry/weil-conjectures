/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.FlatModuleDescent
import Sheaf.AlgebraicGeometry.PullbackModelFlatnessComparison

/-! # Eventual relative flatness on a fixed base-change model

Source: Stacks Project, Tags 05LY and 01JX.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A fixed finitely presented module on a later stage becomes flat at all sufficiently
late stages when its limit base change is flat.
Source: Stacks Project, limits.tex, Tag 05LY; schemes.tex, Tag 01JX (pullback pasting).
(blueprint: lem-pc-staged-module-eventual-flatness).

Proof: apply eventual flatness descent with starting index j, source X_j and structure
map X_j -> Spec R_j. This morphism is the base change of f, so is finitely presented.
The cartesian square defining baseChangeMap identifies X_j times_{Spec R_j} S with X,
and X_j times_{Spec R_j} Spec R_k with X_k. Under these canonical isomorphisms the
pullback of M is precisely moduleBaseChange f applied to M. Transport the assumed
limit flatness to the iterated pullback using these isomorphisms, apply Tag 05LY to M,
and transport its conclusion back. This preserves the universal quantifier over every
k above the threshold. No module, differential, or model is chosen anew. -/
theorem exists_eventually_isFlatOver_staged_module
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    [M.IsFinitePresentation] [M.IsQuasicoherent]
    (hflat : ((Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj M).IsFlatOver
        (pullback.snd f (c.π.app (op i)))) :
    ∃ l : I, ∃ hjl : j ≤ l, ∀ (k : I) (hlk : l ≤ k),
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans (hjl.trans hlk))))))
        (Over.homMk (Spec.map (R.map (homOfLE (hjl.trans hlk))))
          (by simp [← Spec.map_comp, ← R.map_comp]))).obj M).IsFlatOver
            (pullback.snd f
              (Spec.map (R.map (homOfLE (hij.trans (hjl.trans hlk)))))) := by
  let fj := pullback.snd f (Spec.map (R.map (homOfLE hij)))
  let g : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  have hflat' : ((Scheme.Modules.tensorPullback
      (pullback.fst fj (c.π.app (op j)))).obj M).IsFlatOver
        (pullback.snd fj (c.π.app (op j))) :=
    (isFlatOver_tensorPullback_iff_of_isPullback
      (isPullback_baseChangeMap f g) (IsPullback.of_hasPullback fj (c.π.app (op j))) M).mp
        hflat
  obtain ⟨l, hjl, hl⟩ := exists_eventually_isFlatOver_of_limit R c hc j fj M hflat'
  refine ⟨l, hjl, ?_⟩
  intro k hlk
  let gk : Over.mk (Spec.map (R.map (homOfLE (hij.trans (hjl.trans hlk))))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE (hjl.trans hlk))))
      (by simp [← Spec.map_comp, ← R.map_comp])
  exact (isFlatOver_tensorPullback_iff_of_isPullback
    (isPullback_baseChangeMap f gk)
    (IsPullback.of_hasPullback fj (Spec.map (R.map (homOfLE (hjl.trans hlk))))) M).mpr
      (hl k hlk)

end AlgebraicGeometry
