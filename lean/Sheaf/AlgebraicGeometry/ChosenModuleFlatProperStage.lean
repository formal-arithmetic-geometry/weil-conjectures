/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.FlatModuleDescent
import Sheaf.AlgebraicGeometry.ProperSupportDescent
import Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Eventual flatness and proper support of a chosen finite-stage module

Source: Stacks Project, Tags 05LY, 081G, 0CYS, 0032 and 0097.
(blueprint: lem-pc-chosen-module-flat-proper-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A chosen finitely presented module becomes flat with proper support at every later stage.

Source: Stacks Project, Tags 05LY, 081G, 0CYS, 0032 and 0097.
(blueprint: lem-pc-chosen-module-flat-proper-stage).

Proof: View M on X_j with its finitely presented structure morphism to Spec R_j.
Pullback pasting identifies its pullback to the limiting base with the module in the
hypotheses. Tag 05LY gives eventual flatness for this finitely presented module.
Tag 081G gives a stage with proper support, interpreted as properness of the reduced
closed support by Tag 0CYS. Choose an upper bound of the two stages. Cartesian tensor
pullback preserves finite presentation, relative flatness and proper support; hence the
properties hold at every later stage. The tensor-pullback composition isomorphism and
pullback pasting identify these modules with the displayed moduleBaseChange objects.
For a preorder, apply Tag 0032 to choose a final directed poset in its thin filtered
category, with an object mapping above j. Restrict the diagram and its limit to this
poset, apply the preceding argument, and take its image stage in I. For any later stage
of I, the cartesian tensor-pullback preservation theorem transports both properties
from that image stage; no lifting of the later stage through the final functor is needed.
The zero module, an empty source and an empty support cause no exception: tensor
pullback preserves zero and the empty closed subscheme is proper over any base. -/
theorem exists_eventually_chosen_module_flat_proper
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    [M.IsFinitePresentation]
    (hflat : ((Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj M).IsFlatOver
        (pullback.snd f (c.π.app (op i))))
    (hproper : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj M)) :
    ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
      let hjl := hjk.trans hkl
      let B := Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjl)))
          (by simp [← Functor.map_comp, ← Spec.map_comp]))
      (B.obj M).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjl))))) ∧
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (B.obj M) := by sorry

end AlgebraicGeometry
