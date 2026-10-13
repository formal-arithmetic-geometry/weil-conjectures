/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Descent of a proper morphism and a relatively flat finitely presented sheaf

Source: Stacks Project, Tags 0A1H, 05LY and 081F.
(blueprint: lem-pc-proper-flat-single-noetherian-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Geometric Noetherian descent, with no derived category or direct-image assertion.
Source: Stacks Project, Tag 0A1H, Noetherian approximation paragraph, and Tag 081F.

Proof: Choose an affine neighbourhood V of x inside U. Write its coordinate ring as
 the filtered union of its finitely generated Z-subalgebras. Restrict f to V using
 the pullback along V.ι followed by U.ι. Descend this finitely presented morphism and
 the finite presentation of the restricted sheaf to one stage (Tag 01ZM). Enlarge
 the stage so that the descended module is flat over the base (Tag 05LY), and so that
 the descended morphism is proper (Tag 081F). Take T to be the spectrum of this stage
 ring and W its total open. Transport the descended source morphism to W.toScheme
 through the total-open isomorphism. Its source Y is Noetherian, since it is quasi-compact
 and locally of finite type over a Noetherian scheme. The original pullback is the
 base change of Y along g; its projection q gives the displayed cartesian square.
 Descent of the finite presentation gives the indicated sheaf isomorphism. For zero F
 descend the zero sheaf. Empty U has no x; empty X descends the empty source.
(blueprint: lem-pc-proper-flat-single-noetherian-descent). -/
theorem properFlat_single_noetherian_descent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    (U : S.Opens) (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧
      ∃ (T Y : Scheme.{u}) (W : T.Opens),
        IsAffine T ∧ IsCompact (W : Set T) ∧ IsNoetherian W.toScheme ∧
        IsNoetherian Y ∧ ∃ (p : Y ⟶ W.toScheme),
          IsProper p ∧ ∃ (M : Y.Modules),
            M.IsFinitePresentation ∧ M.IsFlatOver p ∧
            ∃ (g : V.toScheme ⟶ W.toScheme)
              (q : pullback f (V.ι ≫ U.ι) ⟶ Y),
              IsPullback q (pullback.snd f (V.ι ≫ U.ι)) p g ∧
              Nonempty (Scheme.Modules.tensorPullbackObj q M ≅
                Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F) := by sorry

end AlgebraicGeometry
