/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentOpen
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.TangentDimensionSmoothness
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.CorankOneCentralizerReductivity
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Openness of reductivity and maximality of a split torus in geometric fibres

Source: Conrad, Reductive Group Schemes (2014), Proposition 3.1.9(1),(2), pp.85--88,
restricted to the split-torus case of (2).
(blueprint: lem-sfb-reductive-torus-fibre-openness).

A geometric point `s : Spec k ⟶ S` represents its underlying point `s (closedPoint k)`.
Every ordinary point has such a lift with k its algebraic residue-field closure.
The identity components below carry the canonical open-subscheme group structure.
Factoring the specified torus map through that open subgroup expresses maximality
inside the identity component, with exactly the original fibre inclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical open neutral component of the group fibre over a field-valued
point. The two local instances merely expose the existing pullback instances.
Source: Conrad, Proposition 3.1.9, pp.85--88; the open identity component is the
existing `GrpObj.identityComponent` construction
(blueprint: lem-sfb-reductive-torus-fibre-openness). -/
noncomputable def groupFibreNeutralComponent {S : Scheme.{u}} (G : Grp (Over S))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S) : Grp (Over (Spec (.of k))) :=
  letI : LocallyOfFiniteType ((Over.pullback s).mapGrp.obj G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom s))
  letI : QuasiCompact ((Over.pullback s).mapGrp.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.snd G.X.hom s))
  Grp.mk (GrpObj.identityComponent ((Over.pullback s).mapGrp.obj G).X)

/-- The canonical open subgroup inclusion of the neutral component into the fibre.
Source: Conrad, Proposition 3.1.9, pp.85--88; this is the existing
`GrpObj.identityComponentι`, bundled as a group-scheme homomorphism
(blueprint: lem-sfb-reductive-torus-fibre-openness). -/
noncomputable def groupFibreNeutralComponentι {S : Scheme.{u}} (G : Grp (Over S))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S) :
    groupFibreNeutralComponent G s ⟶ (Over.pullback s).mapGrp.obj G :=
  letI : LocallyOfFiniteType ((Over.pullback s).mapGrp.obj G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom s))
  letI : QuasiCompact ((Over.pullback s).mapGrp.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.snd G.X.hom s))
  letI : GrpObj ((Over.pullback s).obj G.X) :=
    ((Over.pullback s).mapGrp.obj G).grp
  Grp.homMk (A := groupFibreNeutralComponent G s) (B := (Over.pullback s).mapGrp.obj G)
    (GrpObj.identityComponentι ((Over.pullback s).mapGrp.obj G).X)

/-- Reductivity of a geometric neutral fibre persists near its base point. A given
closed split torus maximal in that neutral fibre stays maximal near the point.
Source: Conrad, Reductive Group Schemes, Proposition 3.1.9(1),(2), pp.85--88
(blueprint: lem-sfb-reductive-torus-fibre-openness).

Proof plan:
1. Work on an affine neighbourhood of the point. The relative component locus of
   the identity section is open by lem-sbc-smooth-section-component-open. Its
   geometric fibres are the canonical neutral components, by
   lem-sfb-solvable-normal-subgroup-products and
   lem-sfb-finite-type-group-identity-subgroup. The group diagrams restrict fibrewise;
   smoothness restricts by lem-weil-pbc-smooth-restrict-open-subschemes. No relative
   affineness of this open subgroup is asserted.
2. For the given split torus T, lem-sfb-relative-torus-centralizer-normalizer gives
   the smooth affine centralizer C. Its special neutral fibre is T by
   lem-sfb-torus-centralizer-smooth-connected and lem-sfb-reductive-torus-self-centralizer.
   Shrink using lem-sfb-smooth-group-fibre-dimension so dim C equals rank T on fibres.
   A larger torus has strictly larger dimension, and cannot fit into C. The same
   dimension argument makes the neutral-fibre torus centralizer equal to T.
3. For reductivity alone, choose a maximal torus by lem-sfb-reductive-borel-pair-structure.
   Lift it after a flat, finitely presented, quasi-finite base change p : S' ⟶ S
   using lem-sfb-geometric-torus-fppf-lift and apply step 2 on an affine
   neighbourhood of the point s' of S' above the original point.
4. Apply lem-sfb-relative-torus-bundle-weights to the adjoint Lie bundle. The special
   weights are zero of rank r and a reduced root set of rank-one nonzero weights by
   lem-sfb-reductive-rank-one-reflections. Shrink to keep all ranks constant.
5. For each root alpha in the finite root set, saturate its integer span in the
   character lattice. Its quotient is free of rank r-1 by primitive-vector integer
   row operations. The associated subtorus K_alpha has invariant Lie rank r+2:
   the zero, alpha and -alpha weights. This works for nonprimitive roots in all
   residue characteristics.
6. The centralizer J_alpha is smooth affine by
   lem-sfb-relative-torus-centralizer-normalizer. Its neutral fibre is the connected
   torus centralizer in the ambient neutral fibre. By
   lem-sfb-group-tangent-dimension-smoothness its dimension is r+2. It contains the
   central rank r-1 torus K_alpha; its special fibre is reductive by
   lem-sfb-reductive-torus-fixed-subgroup.
7. Lift the special reflection of lem-sfb-reductive-rank-one-reflections using the
   smooth normalizer. Intersect its fixed action-matrix locus with the neutral
   component open. Its image is open by lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-pc-smooth-flat and lem-weil-pbc-flat-lfp-open. Intersect these finitely many
   open images. Each fibre then has, after an algebraically closed extension, a
   normalizer point acting nontrivially on the torus.
8. Those corank-one neutral centralizers are nonsolvable: otherwise
   lem-sfb-perfect-solvable-unipotent-torus and lem-sfb-solvable-torus-complements
   identify their torus with the commutative quotient, forcing the normalizer point
   to centralize it. Solvability survives extension by
   lem-sfb-solvable-normal-subgroup-products, so this contradicts step 7.
9. Apply lem-sfb-nonsolvable-central-torus-corank-three to obtain reductivity of
   each corank-one centralizer. Then lem-sfb-corank-one-centralizer-reductivity-test
   proves reductivity of each ambient neutral fibre. The empty root set, rank zero
   and the trivial neutral component are included.
10. Take the open image under p of the final neighbourhood in S', using
    lem-weil-pbc-flat-lfp-open. Each geometric point of this image lifts: its
    nonempty quasi-finite fibre over an algebraically closed field has a rational
    closed point. The lifted fibre is the original geometric fibre, proving the
    first assertion. Step 2 on the original base gives the second assertion.
-/
theorem reductive_torus_fibre_openness
    {S : Scheme.{u}} (G : Grp (Over S))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)
    (hred : ReductiveTorusCentralizer.IsReductive
      (groupFibreNeutralComponent G s)) :
    (∃ U : S.Opens, s (IsLocalRing.closedPoint k) ∈ U ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
        t (IsLocalRing.closedPoint K) ∈ U →
          ReductiveTorusCentralizer.IsReductive
            (groupFibreNeutralComponent G t)) ∧
    (∀ (r : ℕ) (j : relativeSplitTorus S r ⟶ G),
      IsClosedImmersion j.hom.hom.left →
      (∃ i : (Over.pullback s).mapGrp.obj (relativeSplitTorus S r) ⟶
          groupFibreNeutralComponent G s,
        i ≫ groupFibreNeutralComponentι G s =
          (Over.pullback s).mapGrp.map j ∧
        ReductiveTorusCentralizer.IsMaximalTorus i) →
      ∃ V : S.Opens, s (IsLocalRing.closedPoint k) ∈ V ∧
        ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
          t (IsLocalRing.closedPoint K) ∈ V →
          ∃ i : (Over.pullback t).mapGrp.obj (relativeSplitTorus S r) ⟶
              groupFibreNeutralComponent G t,
            i ≫ groupFibreNeutralComponentι G t =
              (Over.pullback t).mapGrp.map j ∧
            ReductiveTorusCentralizer.IsMaximalTorus i) := by
  sorry

end AlgebraicGeometry
