/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Uniqueness of restriction across a depth-positive boundary

Source: Stacks Project, Tags 0B3M and 05AR.
(blueprint: lem-sbc-depth-one-restriction-injective)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Sections are determined by restriction away from a depth-positive boundary.

Source: Stacks Project, Tags 0B3M (restriction avoiding weakly associated points),
05AR (associated and weakly associated points on a locally Noetherian scheme),
and 00LL (depth zero and associated primes).
(blueprint: lem-sbc-depth-one-restriction-injective)

Proof: Work on a Noetherian affine open V. Quasi-coherence identifies the restricted
module with the sheaf of N(V), a finite module by hypothesis. A point of V outside U
cannot be associated to this module: its finite local stalk has positive depth,
whereas an associated maximal ideal forces depth zero. On a Noetherian scheme
associated and weakly associated points coincide. Thus all weakly associated
points of N restricted to V lie in V intersect U. A section vanishing there
has cyclic image subsheaf supported outside U. Its weakly associated points
are both weakly associated to N and in that support, so there are none; the image
is zero. This proves injectivity on affine opens. For arbitrary V, cover V by
affine opens and apply the sheaf separatedness axiom to the two sections.
The unit component is the restriction map by restrictAdjunction_unit_app_app.
This includes the zero sheaf and empty opens. -/
theorem injective_restrictAdjunction_unit_app_of_depth_one
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (1 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y))  :
    ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V) := by sorry

end AlgebraicGeometry.Scheme
