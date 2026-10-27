/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion

/-! # Pointwise smoothness under flat base change

Source: Stacks Project, Morphisms, Tag 02V4, case (2),
`lemma-set-points-where-fibres-smooth`
(blueprint: lem-sfb-scheme-lfp-smooth-flat-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finitely presented scheme morphism is smooth near the image of a
pullback point if and only if its flat base change is smooth near that point.

Source: Stacks Project, Morphisms, Tag 02V4, case (2),
`lemma-set-points-where-fibres-smooth`
(blueprint: lem-sfb-scheme-lfp-smooth-flat-base-change).

Proof:
1. Suppose `f` is smooth on an open neighbourhood `W` of `pullback.fst f g x`.
   By lem-pc-smooth-flat, `W.ι ≫ f` is flat and locally of finite presentation.
   Apply lem-sfb-scheme-flat-smooth-point-base-change to this restricted morphism
   and `g`. By lem-weil-pbc-open-fibre-product its base change is the open
   neighbourhood above `W` in `pullback f g`. This proves ascent.
2. Conversely, smoothness near `x` makes `pullback.snd f g` flat at `x` by
   lem-pc-smooth-flat and the identification of open-subscheme stalks. Since `g`
   is flat, clause (2) of lem-sfb-pointwise-flatness-base-change gives flatness
   of `f` at `pullback.fst f g x` (def-weil-flat-morphism). Clause (3) of
   lem-weil-pbc-qcqs-morphism-permanence makes `pullback.snd f g` locally of
   finite presentation. No global flatness of `f` has been asserted.
3. Use def-pc-scheme-fibre to take the fibre points above `x` and its image.
   By lem-trf-smooth-at-point-fibre-criterion the base-changed fibre is smooth
   near its marked point. By lem-weil-pbc-fibre-of-base-change it is the base
   change of the original fibre along the residue-field map induced by `g`.
   Compatibility with the projections to `U` and injectivity of the fibre
   projection show that the marked points correspond under this comparison.
4. The original fibre morphism is flat by lem-pc-flat-field and locally of
   finite presentation by lem-weil-pbc-qcqs-morphism-permanence (3). Apply
   lem-sfb-scheme-flat-smooth-point-base-change to this fibre morphism and the
   residue-field extension. Smoothness descends to the original fibre point.
5. Apply lem-trf-smooth-at-point-fibre-criterion to `f` at the image of `x`, using
   its assumed local finite presentation, pointwise flatness from step 2 and
   fibre smoothness from step 4. This proves reflection. For an empty pullback
   there are no points to check; `g` need not be surjective or locally finitely
   presented, and `f` need not be flat away from the chosen image point. -/
theorem smooth_at_point_pullback_snd_iff_of_flat_base_change
    {U V T : Scheme.{u}} (f : U ⟶ V) [LocallyOfFinitePresentation f]
    (g : T ⟶ V) [Flat g] (x : pullback (C := Scheme.{u}) f g) :
    (∃ W : (pullback f g).Opens, x ∈ W ∧ Smooth (W.ι ≫ pullback.snd f g)) ↔
      ∃ N : U.Opens, pullback.fst f g x ∈ N ∧ Smooth (N.ι ≫ f) := by
  sorry

end AlgebraicGeometry
