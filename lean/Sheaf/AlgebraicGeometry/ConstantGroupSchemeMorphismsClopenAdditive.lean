/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module
public import Sheaf.AlgebraicGeometry.ConstantGroupScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Component labels of sums of constant group scheme points

Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW).
-/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication carries two component labels to their sum.
Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW).
(blueprint: lem-weil-pbc-constant-group-scheme-point-add-component)
Pair the two points into the fibre square. A point whose two coordinates lie in
components `e` and `e'` belongs to the pair component `(e,e')`. On this component
the multiplication restricts to the base map followed by the inclusion labelled
`e + e'`, so its image lies in that component. The pairing followed by multiplication
is precisely the definition of the point sum. This remains true for an empty domain
or empty base, when there are no points to test. -/
theorem constantGroupSchemePointAdd_component (T U : Scheme.{u}) (E : Type v)
    [Small.{u} E] [AddCommGroup E] (s : U ⟶ T)
    (f g : ConstantGroupSchemePoint T E s) (x : U) (e e' : E)
    (hf : f.1 x ∈ constantGroupSchemeComponent T E e)
    (hg : g.1 x ∈ constantGroupSchemeComponent T E e') :
    (constantGroupSchemePointAdd T E s f g).1 x ∈
      constantGroupSchemeComponent T E (e + e') := by
  classical
  let π := constantGroupSchemeProjection T E
  let l : U ⟶ pullback π π := pullback.lift f.1 g.1 (f.2.trans g.2.symm)
  let C := Scheme.Pullback.openCoverOfLeftRight
    (sigmaOpenCover (fun _ : E ↦ T)) (sigmaOpenCover (fun _ : E ↦ T)) π π
  have hx : l x ∈ (C.f (e, e')).opensRange := by
    rw [Scheme.Pullback.opensRange_openCoverOfLeftRight_f]
    constructor
    · change (pullback.fst π π) (l x) ∈ Set.range (constantGroupSchemeIncl T E e)
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
      exact hf
    · change (pullback.snd π π) (l x) ∈ Set.range (constantGroupSchemeIncl T E e')
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
      exact hg
  obtain ⟨y, hy⟩ := hx
  have hm := (Classical.choose_spec (exists_constantGroupSchemeMultiplication T E)).1
    (e, e')
  refine ⟨(pullback.fst
    (constantGroupSchemeIncl T E e ≫ π)
    (constantGroupSchemeIncl T E e' ≫ π)) y, ?_⟩
  change (constantGroupSchemeIncl T E (e + e')) _ =
    (constantGroupSchemeMultiplication T E) (l x)
  rw [← hy, ← Scheme.Hom.comp_apply]
  exact (congrArg (fun h ↦ h y) hm).symm
end AlgebraicGeometry
