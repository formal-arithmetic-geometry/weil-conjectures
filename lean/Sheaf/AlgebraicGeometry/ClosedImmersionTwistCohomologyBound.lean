/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # A step in projective Serre vanishing -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard N+1 affine opens bound cohomology of a closed projective subscheme.
Source: Stacks Project, Tags 01XT and 01YS (4).
(blueprint: lem-pc-j4-closed-immersion-twist-cohomology-bound)

Proof: Restrict the N+1 standard affine opens to X. A closed subscheme of an affine
scheme is affine. Their intersections are affine because X is separated. The twisted
module is quasi-coherent, so its higher cohomology on each intersection is zero.
The ordered Cech complex computes cohomology and its terms, indexed by strictly
increasing tuples of distinct cover indices, are zero in all degrees above N. Hence
cohomology is zero above N, for every twist, including
zero; no finite presentation is needed for this cover argument. -/
theorem isZero_closedImmersion_twist_above_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (q t : ℕ) (hq : N < q) :
    IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
      (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by sorry

end AlgebraicGeometry.Scheme.Modules
