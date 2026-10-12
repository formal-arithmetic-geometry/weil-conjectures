/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus
import Sheaf.AlgebraicGeometry.ProperNormalizedFibres

/-! # Representing the universal rank clause

Source: Stacks Project, Tag 0BDP (blueprint: lem-sc-picard-universal-rank-match-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The universal rank clause alone is represented by a finitely presented immersion.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, and Tags 0B91 and 0BDL.
(blueprint: lem-sc-picard-universal-rank-match-locus)

Proof: The structure-sheaf unit implies that every fibre is nonempty and connected,
since its global functions form the residue field and thus have no nontrivial idempotent.
Finite local freeness makes each rank locus in X open and closed. Flat finite presentation
makes its image open, and properness makes the image closed. Connectedness makes these
images disjoint. They cover S and give its open-and-closed rank decomposition.
On a rank-r component the module and its dual are relatively flat and finitely presented.
Tag 0B91 gives perfect derived direct images with arbitrary derived base change. Their
cohomology in negative degrees vanishes after every base change, so locally they have Tor
amplitude [0,b]. Apply Tag 0BDL at degree zero and rank r to each of the two complexes.
Their fibre product represents the conjunction of their universal rank-r conditions.
The comparison of degree-zero derived direct image with ordinary pushforward identifies
that conjunction with the displayed rank clause. On a test scheme, refine the open covers
for the two direct images and the pullback of E to obtain one common neighbourhood.
The rank of E fixes r, because every fibre over this component is nonempty. The universal
property also applies to nonreduced test schemes. On overlapping amplitude charts these
immersions have unique representing identifications, which satisfy the cocycle identity,
so they glue. Take their disjoint union over the rank components. Immersion and local
finite presentation are local on the target. A quasi-compact target open meets only
finitely many rank components; the finite-presentation rank loci on each component are
quasi-compact, so the glued immersion is quasi-compact. Rank zero uses a zero first term;
empty test schemes impose no rank constraints. No base-change-map isomorphism is asserted.
-/
theorem exists_picardUniversalRankMatchLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g := by sorry

end AlgebraicGeometry.Scheme
