/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.PerfectComplexDescent
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Perfect descent refining a cartesian model

Source: Stacks Project, Tags 0032 and 09RF.
(blueprint: lem-pc-filtered-cartesian-perfect-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A perfect object descends to a base-change refinement of a fixed cartesian
finite-presentation model. The comparison also records the triangle to the old model.
There is no complex of base-flat modules in this assertion.

Proof:
1. Restrict the ring diagram to the under-category of i, then to a final directed
   poset (Tag 0032). Both functors are final; thus the restricted cocone has the
   same colimit, and its stage rings are Noetherian.
2. Identify X with the canonical pullback of Xi along Spec(c.ι.app i), using
   hcart. Transport E through this scheme isomorphism by derived pullback;
   perfectness is preserved under an isomorphism.
3. Apply perfect_complex_descends (Tag 09RF) to the directed diagram, starting
   with the pullback of Xi to an object of the under-category. This produces a
   perfect object at a later stage and its derived-pullback isomorphism to E.
4. Return the stage to I. Put Xj equal to the pullback of Xi along its recorded
   transition. Let p be the first projection and fj the second. Obtain gj by
   the universal property of this pullback, using the cocone equation and hcart.
   Pullback pasting gives its cartesian square to X; the first projection equation
   gives gj ≫ p = g. Finite presentation, quasi-compactness and quasi-separatedness
   of fj follow by base change. Derived pullback composition and the isomorphism
   of step 2 give the final comparison with the original E.
Source: Stacks Project, Tags 0032 and 09RF.
(blueprint: lem-pc-filtered-cartesian-perfect-descent).
-/
theorem filtered_cartesian_perfect_descent
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c)
    (X : Scheme.{u}) (f : X ⟶ Spec c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ (Z : Scheme.{u}), HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (g : X ⟶ Xi) (hcart : IsPullback g f fi (Spec.map (c.ι.app i)))
    (E : schemeDerivedCategory X) (hE : X.IsPerfect E) :
    ∃ (j : I) (a : i ⟶ j) (Xj : Scheme.{u}) (fj : Xj ⟶ Spec (R.obj j)),
      LocallyOfFinitePresentation fj ∧ QuasiCompact fj ∧ QuasiSeparated fj ∧
      ∃ (_hfj : LocallyOfFiniteType fj) (p : Xj ⟶ Xi) (gj : X ⟶ Xj),
        IsPullback p fj fi (Spec.map (R.map a)) ∧ gj ≫ p = g ∧
        IsPullback gj f fj (Spec.map (c.ι.app j)) ∧
        ∃ Ej : schemeDerivedCategory Xj, Xj.IsPerfect Ej ∧
          Nonempty ((derivedPullback gj).obj Ej ≅ E) := by
  classical
  obtain ⟨A, hAorder, hAdir, hAnonempty, F, hFfinal⟩ :=
    IsFiltered.exists_directed (Under i)
  let : PartialOrder A := hAorder
  let : IsDirected A (· ≤ ·) := hAdir
  let : Nonempty A := hAnonempty
  have : F.Final := hFfinal
  let H := F ⋙ Under.forget i
  let R' := H ⋙ R
  let c' := c.whisker H
  have hc' : IsColimit c' := (Functor.Final.isColimitWhiskerEquiv H c).symm hc
  let (b : A) : IsNoetherianRing (R'.obj b) := by dsimp [R', H]; infer_instance
  let b₀ : A := Classical.choice hAnonempty
  let t₀ : Spec (R'.obj b₀) ⟶ Spec (R.obj i) := Spec.map (R.map (F.obj b₀).hom)
  let X₀ := pullback fi t₀
  let f₀ : X₀ ⟶ Spec (R'.obj b₀) := pullback.snd fi t₀
  have hbase : Spec.map (c'.ι.app b₀) ≫ t₀ = Spec.map (c.ι.app i) := by
    dsimp [t₀, c', H]
    rw [← Spec.map_comp, c.w]
  have hcart₀ : IsPullback g f fi (Spec.map (c'.ι.app b₀) ≫ t₀) := by
    rw [hbase]
    exact hcart
  let g₀ : X ⟶ X₀ := (IsPullback.of_hasPullback fi t₀).lift g (f ≫ Spec.map (c'.ι.app b₀))
    (by rw [Category.assoc, hbase]; exact hcart.w)
  have hsquare₀ : IsPullback g₀ f f₀ (Spec.map (c'.ι.app b₀)) :=
    hcart₀.of_right' (IsPullback.of_hasPullback fi t₀)
  let e₀ := hsquare₀.isoPullback
  let E₀ := (derivedPullback e₀.inv).obj E
  have hE₀ : (pullback f₀ (Spec.map (c'.ι.app b₀))).IsPerfect E₀ :=
    derivedPullback_preserve_perfect e₀.inv E hE
  obtain ⟨b, hle, Eb, hEb, ⟨eEb⟩⟩ :=
    perfect_complex_descends R' c' hc' b₀ X₀ f₀ E₀ hE₀
  let t : Spec (R'.obj b) ⟶ Spec (R'.obj b₀) := Spec.map (R'.map (homOfLE hle))
  let Xb := pullback f₀ t
  let fb : Xb ⟶ Spec (R'.obj b) := pullback.snd f₀ t
  let p : Xb ⟶ Xi := pullback.fst f₀ t ≫ pullback.fst fi t₀
  have htrans : t ≫ t₀ = Spec.map (R.map (F.obj b).hom) := by
    dsimp [t, t₀, R', H]
    rw [← Spec.map_comp, ← R.map_comp]
    congr 2
    exact Under.w (F.map (homOfLE hle))
  have hp : IsPullback p fb fi (Spec.map (R.map (F.obj b).hom)) := by
    rw [← htrans]
    exact (IsPullback.of_hasPullback f₀ t).paste_horiz
      (IsPullback.of_hasPullback fi t₀)
  have hbaseb : Spec.map (c'.ι.app b) ≫ Spec.map (R.map (F.obj b).hom) =
      Spec.map (c.ι.app i) := by
    dsimp [c', H]
    rw [← Spec.map_comp, c.w]
  let gb : X ⟶ Xb := hp.lift g (f ≫ Spec.map (c'.ι.app b))
    (by rw [Category.assoc, hbaseb]; exact hcart.w)
  have hgp : gb ≫ p = g := hp.lift_fst _ _ _
  have hgcart : IsPullback gb f fb (Spec.map (c'.ι.app b)) := by
    have hh : IsPullback g f fi
        (Spec.map (c'.ι.app b) ≫ Spec.map (R.map (F.obj b).hom)) := by
      rw [hbaseb]
      exact hcart
    exact hh.of_right' hp
  refine ⟨H.obj b, (F.obj b).hom, Xb, fb, inferInstance, inferInstance,
    inferInstance, inferInstance, p, gb, hp, hgp, hgcart, Eb, hEb, ?_⟩
  let v : Over.mk (Spec.map (c'.ι.app b₀)) ⟶ Over.mk t :=
    Over.homMk (Spec.map (c'.ι.app b))
      (by dsimp [t]; rw [← Spec.map_comp, c'.w (homOfLE hle)])
  let bm := baseChangeMap f₀ v
  have hb1 : bm ≫ pullback.fst f₀ t = pullback.fst f₀ (Spec.map (c'.ι.app b₀)) :=
    baseChangeMap_fst f₀ v
  have hb2 : bm ≫ pullback.snd f₀ t =
      pullback.snd f₀ (Spec.map (c'.ι.app b₀)) ≫ Spec.map (c'.ι.app b) :=
    baseChangeMap_snd f₀ v
  have hcan : e₀.hom ≫ bm = gb := by
    apply hp.hom_ext
    · change (e₀.hom ≫ bm) ≫ (pullback.fst f₀ t ≫ pullback.fst fi t₀) = gb ≫ p
      rw [Category.assoc, ← Category.assoc bm, hb1,
        ← Category.assoc, hsquare₀.isoPullback_hom_fst, hgp]
      exact (IsPullback.of_hasPullback fi t₀).lift_fst _ _ _
    · change (e₀.hom ≫ bm) ≫ pullback.snd f₀ t = gb ≫ fb
      rw [Category.assoc, hb2, ← Category.assoc,
        hsquare₀.isoPullback_hom_snd]
      exact (hp.lift_snd _ _ _).symm
  obtain ⟨_, _, _, comp, _, unit, _, _, _⟩ := exists_derivedPullbackComposition
  exact ⟨eqToIso (congrArg (fun q ↦ (derivedPullback q).obj Eb) hcan.symm) ≪≫
    ((comp e₀.hom bm).app Eb).symm ≪≫ (derivedPullback e₀.hom).mapIso eEb ≪≫
      (comp e₀.hom e₀.inv).app E ≪≫
      eqToIso (congrArg (fun q ↦ (derivedPullback q).obj E) e₀.hom_inv_id) ≪≫
      (unit X).app E⟩

end AlgebraicGeometry
