/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentPreorderStage
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.PullbackModelFlatnessComparison

/-! # Flat-module descent over a directed preorder

## References

* Stacks Project, Tags 05LY, 0032, 01U8, 01JX and 0097
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Relative flatness of a fixed finitely presented module descends over a directed preorder
(Stacks, Tags 05LY, 0032, 01U8, 01JX and 0097). -/
theorem exists_eventually_isFlatOver_of_isPullback_limit_preorder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation]
    {X : Scheme.{u}} (a : X ⟶ Xi) (b : X ⟶ c.pt)
    (hcart : IsPullback a b f (c.π.app (op i)))
    (hflat : ((Scheme.Modules.tensorPullback a).obj M).IsFlatOver b) :
    ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k)
      {Y : Scheme.{u}} (p : Y ⟶ Xi) (q : Y ⟶ Spec (R.obj k)),
      IsPullback p q f (Spec.map (R.map (homOfLE (hij.trans hjk)))) →
      ((Scheme.Modules.tensorPullback p).obj M).IsFlatOver q := by
  let ac := pullback.fst f (c.π.app (op i))
  let bc := pullback.snd f (c.π.app (op i))
  have hcanon : ((Scheme.Modules.tensorPullback ac).obj M).IsFlatOver bc := by
    exact (isFlatOver_tensorPullback_iff_of_isPullback hcart
      (IsPullback.of_hasPullback f (c.π.app (op i))) M).mp hflat
  obtain ⟨j, hij, hj⟩ :=
    exists_isFlatOver_of_isPullback_limit_preorder_stage R c hc i f M hcanon
  refine ⟨j, hij, ?_⟩
  intro k hjk Y p q hq
  let gj := Spec.map (R.map (homOfLE hij))
  let gk := Spec.map (R.map (homOfLE (hij.trans hjk)))
  let t := Spec.map (R.map (homOfLE hjk))
  let aj := pullback.fst f gj
  let bj := pullback.snd f gj
  let N := (Scheme.Modules.tensorPullback aj).obj M
  have : N.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorPullback aj M
  have hN : N.IsFlatOver bj := hj
  have hbase := relativelyFlat_module_pullback bj t N hN
  let d := pullback.fst bj t
  let e := pullback.snd bj t
  have hpaste : IsPullback (d ≫ aj) e f gk := by
    have h := (IsPullback.of_hasPullback bj t).paste_horiz
      (IsPullback.of_hasPullback f gj)
    simpa [d, e, aj, bj, gj, gk, t, ← Spec.map_comp, ← R.map_comp] using h
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp d aj
  have hcomp : ((Scheme.Modules.tensorPullback (d ≫ aj)).obj M).IsFlatOver e :=
    hbase.of_iso (δ.app M).symm
  exact (isFlatOver_tensorPullback_iff_of_isPullback hpaste hq M).mp hcomp

end AlgebraicGeometry
