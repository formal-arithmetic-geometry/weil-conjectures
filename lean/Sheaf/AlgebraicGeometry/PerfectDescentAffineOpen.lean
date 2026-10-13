/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.Algebra.Homology.AffinePerfectColimitDescent
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # PerfectDescentAffineOpen

Source: Stacks Project, Tag 09RF (blueprint: lem-pc-perfect-descent-affine-open).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Perfect complexes descend on an affine open, and on the empty open.
Source: Stacks Project, Tag 09RF, affine case; Tag 0BC7 and Tag 08EB
(blueprint: lem-pc-perfect-descent-affine-open).

Proof: An open immersion with affine image identifies its source with that affine
subscheme. Its quasi-compactness makes the composite with `s` finitely presented.
On the tail above `i`, the coordinate rings of its base changes form a filtered
system whose colimit is the coordinate ring at `c.pt`. A perfect complex has
quasi-coherent cohomology; Tag 08EB represents it by a bounded finite projective
complex. Tag 0BC7 descends the finitely many terms, splittings, differentials and
relations to a stage above `i`. Sheafify that complex. Its terms are locally direct
summands of finite free modules, so it is perfect. They are flat, so ordinary
pullback computes derived pullback; the scalar-extension isomorphism gives the
required derived isomorphism. Transport along the affine identifications. For the
empty open, every base change is empty and its module sheaves, hence its derived
category, are zero: choose the zero object at stage `i`, and use its unique
isomorphism to `E`. These transports apply to every open-immersion presentation. -/
theorem perfect_descent_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (U : Xi.Opens) (hU : IsAffineOpen U ∨ U = ⊥) :
    PerfectDescentOnOpen R c i Xi s U := by sorry

end AlgebraicGeometry
