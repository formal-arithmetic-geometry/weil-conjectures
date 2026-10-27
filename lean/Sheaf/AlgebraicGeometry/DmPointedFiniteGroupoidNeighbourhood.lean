/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.DmStabilizerIsomorphismOpenLocus
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Pointed finite-groupoid neighbourhoods of Deligne--Mumford stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU4
(lemma-etale-local-quasi-DM-at-x), specialized to finite-inertia DM stacks;
Tags 0CL0 and 06N3 (blueprint: lem-sfb-dm-pointed-finite-groupoid-neighbourhood).

The quotient retains its fppf presentation. Stabilizer preservation is imposed only
at the chosen point, using the existing geometric-stabilizer isomorphism locus.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A finite-inertia DM stack has, at each point, a representable etale neighbourhood
presented by an affine groupoid with finite locally free source and target, and the
map identifies the geometric stabilizers at the chosen point.

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU4
(lemma-etale-local-quasi-DM-at-x), Tags 0CL0 and 06N3
(blueprint: lem-sfb-dm-pointed-finite-groupoid-neighbourhood).

Proof:
1. Choose an etale scheme atlas and an affine open V through a lift of x, using
   lem-weil-pbc-affine-opens-basis and lem-weil-pbc-open-immersion-etale.
   The stack-chartwise calculus makes V -> X etale. Apply
   lem-sfb-dm-finite-inertia-affine-relation: its self-relation has separated,
   flat, locally finitely presented, locally quasi-finite projections, and its
   stabilizer at the chosen lift is finite. Finite inertia supplies this without
   quasi-compactness of X or separatedness of S.
2. Apply lem-sfb-etale-groupoid-affine-stabilizer-splitting. After an affine etale
   pointed neighbourhood V' -> V there is an open wide subgroupoid P of the
   pulled-back relation whose projections are finite locally free and which
   contains the entire stabilizer fibre. The pulled-back relation is the actual
   self-relation V' x_X V': an arrow and its two lifts give the same isomorphism
   in X, and conversely that isomorphism with the two lifts recovers the arrow.
   These inverse constructions respect pullback and composition.
3. By lem-sfb-dm-finite-inertia-affine-relation, the full relation quotient is a
   DM open substack of X. Apply lem-sfb-open-subgroupoid-etale-quotient to obtain
   Q = [V'/P], DM and representable etale over that open. Composition gives g.
   The arrow scheme P is affine since it is finite over affine V', by
   lem-weil-pbc-finite-morphism-permanence. Take U = V' and R = P.
4. Let q be the image of the chosen lift. It maps to x. The self-relation of
   U -> Q is P by lem-sfb-fppf-groupoid-stack-presentations. Thus the stabilizer
   map is exactly the inclusion of the P-stabilizer fibre into the stabilizer
   of U x_X U, by lem-sfb-dm-finite-inertia-affine-relation. P contains that entire
   fibre, so this open restriction is the whole scheme, with its structure sheaf
   and group operations. Base change to an algebraic closure identifies geometric
   stabilizer group spaces. This is the existing stabilizer-isomorphism locus:
   the map on fibre automorphism groups is bijective; the DM stabilizers over an
   algebraically closed field are etale, so their group-space map is an isomorphism.
   No assertion is made about other points. -/
theorem exists_dm_pointed_finite_groupoid_neighbourhood {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsDeligneMumfordModuliStack X)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X))
    (x : ModuliPoints X) :
    ∃ (U R : Over S) (s t : R ⟶ U) (e : U.left ⟶ R.left)
      (i : R.left ⟶ R.left) (c : pullback s.left t.left ⟶ R.left),
      IsAffine U.left ∧ IsAffine R.left ∧
      IsGroupoidScheme s.left t.left e i c ∧
      s.left.IsFiniteLocallyFree ∧ t.left.IsFiniteLocallyFree ∧
      ∃ (Q : BasedCategory.{max u v, max (u + 1) w} (Over S))
        (a : BasedFunctor (discreteModuli (yoneda.obj U)) Q),
        Nonempty (SchemeGroupoidQuotientPresentation s t e i c Q a) ∧
        IsDeligneMumfordModuliStack Q ∧
        ∃ (g : BasedFunctor Q X) (q : ModuliPoints Q),
          IsRepresentableByAlgebraicSpaces g ∧ IsEtaleModuliMap g ∧
          moduliPointMap g q = x ∧ q ∈ moduliStabilizerIsomorphismLocus g := by
  sorry

end CategoryTheory
