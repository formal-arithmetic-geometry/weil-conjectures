/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Mathlib.CategoryTheory.Presentable.Directed
import Sheaf.AlgebraicGeometry.FlatModuleDescent
import Sheaf.AlgebraicGeometry.ProperSupportDescent
import Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Refining an already chosen complex to flat terms with proper support

Source: Stacks Project, Tags 05LY, 081G and 0CYS; tensor pullback functoriality.
(blueprint: lem-pc-chosen-complex-flat-proper-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Refine an already chosen bounded finitely presented complex at stage `j`.
This statement does not descend a complex from the limit: the entire finite-stage
complex `H`, including its differentials, is an input. Its limit pullback is assumed
flat with proper support. The output identifies the new limit pullback with the
pullback of this particular `H`, compatibly with all differentials.

Source: Stacks Project, Limits of Schemes, Tag 05LY and Tag 081G; Cohomology of
Schemes, Tag 0CYS; pullback pasting and tensor pullback functoriality.
(blueprint: lem-pc-chosen-complex-flat-proper-refinement).

Proof: choose bounds `a,b` for `H`. For each degree in the finite integer interval
`[a,b]`, regard its term as a finitely presented module on `X_j`. Pullback pasting
identifies its limit pullback with the displayed module base change. Tag 05LY gives
a stage where that chosen term is flat, and Tag 081G gives a stage where its support
is proper, using Tag 0CYS to interpret proper support. Both properties persist under
further base change. Choose one common upper bound of `j` and these finitely many
stages by directedness. Outside the interval the terms are zero, with flat sections
and empty proper support, so impose no additional stage condition. Pull back `H`
to this common stage using the additive tensor pullback functor on complexes.
Pullback preserves zero objects and finite presentation, so this complex is bounded
and finitely presented. Its terms are flat with proper support by the choice of stage.
The composition isomorphism of tensor pullback, together with pullback pasting,
identifies its limit pullback with that of `H`; naturality gives the equation for each
differential. If the interval is empty, take `j` itself. For a preorder, restrict to a final
directed poset in its thin filtered category (Tag 0032); finality preserves the limit.
Apply the directed-poset argument there and return the resulting stage through the
final functor. Thus antisymmetry is not an assumption. -/
theorem exists_chosen_complex_flat_proper_refinement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (H : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ)
    (hH_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n))
    (hH_fp : ∀ n : ℤ, (H.X n).IsFinitePresentation)
    (hH_flat : ∀ n : ℤ,
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n)).IsFlatOver
        (pullback.snd f (c.π.app (op i))))
    (hH_support : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n))) :
    ∃ (k : I) (hjk : j ≤ k)
      (K : CochainComplex
        (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
      (∀ n : ℤ, (K.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (K.X n).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))))) ∧
      (∀ n : ℤ, Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) (K.X n)) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))).obj
            (K.X n) ≅
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n),
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))).map
            (K.d n m) ≫ (e m).hom =
          (e n).hom ≫ (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (H.d n m) := by sorry

end AlgebraicGeometry
