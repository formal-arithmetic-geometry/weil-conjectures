/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Paper.StrictPerfectRingedPullbackModel
import Sheaf.Paper.SheafSliceDerivedComparison
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.Algebra.Homology.AffinePerfectColimitDescent
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Paper.ProjectionMateExact

/-! # Perfect derived objects on affine inverse limits of algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 09RH and 09RJ;
sites-cohomology.tex, Tag 08H6
(blueprint: lem-sfb-space-perfect-limit-category).

The Hom-colimit bijection is stated elementwise: morphisms descend, and equality
of two stage morphisms after limit pullback holds at a later stage. Applied at every
stage, these are precisely surjectivity and injectivity of the directed Hom-colimit
map. All transports are the existing universal-counit-normalized pullback comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison between iterated pullback through a stage and pullback to the limit.
Source: Stacks Project, Tag 09RJ, with the canonical compositions of Tag 0D6D
(blueprint: lem-sfb-space-perfect-limit-category). -/
def perfectLimitPullbackComparison
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (c : Cone D)
    [∀ i : Iᵒᵖ, HasDerivedCategory.{w} (D.obj i).SmallModules]
    [HasDerivedCategory.{w} c.pt.SmallModules]
    {i j : I} (hij : i ≤ j) (E : (D.obj (op i)).DerivedModules) :
    (spaceDerivedPullback (X := c.pt) (c.π.app (op j))).obj
        ((spaceDerivedPullback (D.map (homOfLE hij).op)).obj E) ≅
      (spaceDerivedPullback (X := c.pt) (c.π.app (op i))).obj E :=
  (spaceDerivedPullbackComp (Z := c.pt)
      (D.map (homOfLE hij).op) (c.π.app (op j))).symm.app E ≪≫
    eqToIso (congrArg (fun f ↦ (spaceDerivedPullback f).obj E) (c.w (homOfLE hij).op))

/-- Derived tensor pullback preserves perfect objects for every morphism of spaces.
Source: Stacks Project, sites-cohomology.tex, Tag 08H6
(blueprint: lem-sfb-space-perfect-limit-category).

Proof: choose the local bounded finite-free-retract models in the definition of
perfectness. By lem-weil-pbc-strict-perfect-ringed-pullback-model each model is K-flat,
has flat terms, and its termwise pullback computes derived pullback, retaining the
splittings and degree bounds. By lem-sbc-ringed-topos-sheaf-slice-derived-comparison
this computation agrees with restriction to the pulled-back local sites. Inverse images
of the covering form a covering. These pulled-back models therefore exhibit the local
perfectness of the pullback. The small ringed model equivalence transports the same
models and their splittings; no flatness of the space morphism is assumed. -/
theorem isPerfect_spaceDerivedPullback
    {X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (E : Y.DerivedModules)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      Y.smallStructureSheaf E) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf ((spaceDerivedPullback f).obj E) := by
  sorry

/-- Perfect objects and their derived morphisms descend along affine inverse limits.
The last two clauses are the elementwise form of the canonical Hom-colimit bijection.

Source: Stacks Project, spaces-perfect.tex, Tags 09RH and 09RJ
(blueprint: lem-sfb-space-perfect-limit-category).

Proof:
1. Perfect objects have quasi-coherent cohomology by lem-sfb-space-perfect-objects-compact.
   Apply lem-sfb-space-perfect-source-hom-continuity to the two perfect stage objects.
   This gives the displayed morphism descent and eventual equality clauses. The latter
   is precisely the equality relation in a directed colimit of sets.
2. Fix a stage i0. For every qcqs etale space T0 over that stage, let P(T0) mean that
   perfect objects on its limit base change descend. By
   lem-sfb-space-affine-limits-schematic-stages these base changes have the asserted
   limits and affine transitions. A finite affine etale atlas and its quasi-compact
   overlaps show that the base changes are qcqs. Directed tails are nonempty and cofinal.
3. If T0 is affine, all stages and the limit are affine schemes. By
   lem-weil-pbc-limit-affine-transition their rings form the filtered colimit ring.
   Use lem-sfb-derived-etale-zariski-equivalence and lem-sfb-etale-detects-perfect
   to pass to a perfect Zariski object. By lem-pc-perfect-affine-bounded-projective
   it has a bounded finite-projective model. Descend that model using
   lem-pc-affine-perfect-colimit-descent. Its terms are flat and it is K-flat.
   The tensor-tilde computation of lem-pc-affine-derived-pullback-tensor-tilde and
   the etale/Zariski pullback comparison identify its pullback with the original
   object. The empty affine uses the zero complex.
4. For a distinguished square, descend the two local perfect objects to a common
   stage. On the overlap descend their comparison and inverse by Step 1, using
   lem-sbc-ringed-topos-sheaf-slice-derived-comparison for the canonical restrictions.
   Eventual equality makes the inverse identities hold at a later common stage.
   Pullback preserves perfectness by isPerfect_spaceDerivedPullback.
5. Let q be the limit projection at that stage. Adjunction gives maps from the two
   local objects to Rq_*E. Their overlap compatibility follows from the restriction
   comparison and mate identity of lem-sbc-ringed-topos-sheaf-slice-derived-comparison.
   The unbounded adjunction is that of lem-weil-pbc-ringed-projection-mate-exact.
   Apply lem-sfb-space-distinguished-derived-gluing, with target Rq_*E, to obtain a
   stage object and a map from it to Rq_*E restricting to those two maps.
6. The two local models show that this stage object is perfect. The adjoint map from
   its pullback to E restricts to the two chosen isomorphisms, by the same mate identity.
   Its cone has zero cohomology on an etale cover, hence is zero, so it is an isomorphism.
7. Apply lem-sfb-space-qcqs-distinguished-square-induction to Steps 3--6, with T0 equal
   to the chosen stage. This proves object descent. Step 1 proves the Hom assertion.
-/
theorem perfect_descent_affineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over (Spec (.of (ULift.{u} ℤ))))
      (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
        CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), MapIsAffine (D.map f))
    (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, HasDerivedCategory.{w} (D.obj i).SmallModules]
    [HasDerivedCategory.{w} c.pt.SmallModules] :
    (∀ E : c.pt.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        c.pt.smallStructureSheaf E →
      ∃ (i : I) (E_i : (D.obj (op i)).DerivedModules),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
          (D.obj (op i)).smallStructureSheaf E_i ∧
        Nonempty ((spaceDerivedPullback (X := c.pt) (c.π.app (op i))).obj E_i ≅ E)) ∧
    (∀ (i : I) (E_i F_i : (D.obj (op i)).DerivedModules),
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        (D.obj (op i)).smallStructureSheaf E_i →
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        (D.obj (op i)).smallStructureSheaf F_i →
      (∀ f : (spaceDerivedPullback (X := c.pt) (c.π.app (op i))).obj E_i ⟶
          (spaceDerivedPullback (X := c.pt) (c.π.app (op i))).obj F_i,
        ∃ (j : I) (hij : i ≤ j)
          (f_j : (spaceDerivedPullback (D.map (homOfLE hij).op)).obj E_i ⟶
            (spaceDerivedPullback (D.map (homOfLE hij).op)).obj F_i),
          (perfectLimitPullbackComparison D c hij E_i).inv ≫
            (spaceDerivedPullback (X := c.pt) (c.π.app (op j))).map f_j ≫
            (perfectLimitPullbackComparison D c hij F_i).hom = f) ∧
      (∀ f g : E_i ⟶ F_i,
        (spaceDerivedPullback (X := c.pt) (c.π.app (op i))).map f =
          (spaceDerivedPullback (X := c.pt) (c.π.app (op i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (spaceDerivedPullback (D.map (homOfLE hij).op)).map f =
            (spaceDerivedPullback (D.map (homOfLE hij).op)).map g)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
