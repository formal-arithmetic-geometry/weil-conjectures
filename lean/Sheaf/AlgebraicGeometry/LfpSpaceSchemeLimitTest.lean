/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # Maps from qcqs scheme limits to locally finitely presented algebraic spaces

Source: Stacks Project, Limits of Spaces, Tags 04AK and 0CP4
(blueprint: lem-sfb-lfp-space-scheme-limit-test).

Evaluation of the algebraic space on an S-scheme is its set of S-morphisms by Yoneda.
The comparison below is induced by the actual limit projections. Local finite presentation
is tested on étale scheme charts of Z; the target chart is the identity chart of S.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical restriction map is bijective, every map factors through a stage, and
maps at any two stages have equal restrictions exactly when they agree at a later common
stage. The schemes in the system need only be qcqs, with affine transition morphisms;
there is no compactness or separation assumption on Z.

Source: Stacks Project, Limits of Spaces, Tags 04AK and 0CP4
(blueprint: lem-sfb-lfp-space-scheme-limit-test).

Proof:
1. The étale chart test [lem-sfb-space-local-properties-chart-test] and the relative
   affine criterion [lem-sfb-space-relative-affine-limit-criterion], applied to Z → S,
   give the assertion for affine systems: maps to S form a singleton, including their
   filtered colimit. Interpret its bijection elementwise using
   [lem-weil-pbc-filtered-colimit-sets-elementwise].
2. Choose a stage and a finite affine open cover with quasi-compact intersections
   [lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings]. Cover each intersection by
   finitely many affine opens [lem-pqf-finite-affine-cover-qc-open]. On the cofinal tail,
   all inverse images of these opens are affine, and their inverse-image systems have
   the required limits [pqf-def-affine-morphism, lem-weil-pbc-limit-affine-transition].
   Common upper bounds show that passing to the tail changes neither the limit nor
   eventual equality.
3. Descend a given limit section separately on each affine open by step 1. A common
   upper bound gives one stage. On the finitely many affine opens covering pairwise
   intersections, step 1 detects equality eventually; choose one later stage for all
   these compatibilities [lem-weil-pbc-filtered-colimit-sets-elementwise].
4. Open covers are fppf covers [lem-pc-zariski-coverings-are-fppf]. The sheaf equalizer
   first gives equality on each whole intersection, then glues the local sections
   [def-trf-algebraic-space, def-weil-pbc-sites-and-cohomology]. Uniqueness shows that
   the resulting section restricts to the original one on the limit, proving surjectivity.
5. For two stage sections with equal limit restrictions, pass to a common stage and a
   finite affine cover. Step 1 detects equality on each affine inverse-image system.
   A common later stage makes all finitely many equalities hold, and sheaf uniqueness
   gives equality on that stage. Conversely restriction preserves equality. The filtered
   colimit representative and equality criteria now prove injectivity and the two
   elementwise clauses. For empty sources the empty cover has a unique matching family,
   so the same argument applies. -/
theorem lfp_space_scheme_limit_test {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (hlfp : ∀ (V : Over S) (a : yoneda.obj V ⟶ Z.obj.obj),
      IsEtale a → LocallyOfFinitePresentation V.hom)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i).left]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) :
    Function.Bijective
        (colimit.desc (D.rightOp ⋙ Z.obj.obj)
          (Z.obj.obj.mapCocone (coconeRightOpOfCone c))) ∧
      (∀ g : Z.obj.obj.obj (op c.pt),
        ∃ (i : I) (a : Z.obj.obj.obj (op (D.obj (op i)))),
          Z.obj.obj.map (c.π.app (op i)).op a = g) ∧
      (∀ (i j : I) (a : Z.obj.obj.obj (op (D.obj (op i))))
          (b : Z.obj.obj.obj (op (D.obj (op j)))),
        Z.obj.obj.map (c.π.app (op i)).op a = Z.obj.obj.map (c.π.app (op j)).op b ↔
          ∃ (k : I) (hi : i ≤ k) (hj : j ≤ k),
            Z.obj.obj.map (D.map (homOfLE hi).op).op a =
              Z.obj.obj.map (D.map (homOfLE hj).op).op b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
