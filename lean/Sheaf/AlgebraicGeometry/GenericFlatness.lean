/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties

/-! # Generic flatness for finite type morphisms

Source: Stacks Project, Tag 052A.
(blueprint: lem-sbc-generic-flatness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type morphism to an integral scheme is flat over a nonempty open.

Source: Stacks Project, Tag 052A, with the structure sheaf as the finite type module.
Proof: choose a nonempty affine open of the integral base, with coordinate domain A.
Quasi-compactness gives a finite affine cover of its inverse image, with coordinate
rings B_i finite type over A. Generic freeness, in the version for a finite type
algebra over an arbitrary domain (Tag 051T), gives nonzero elements a_i of A such
that each localized algebra (B_i)_{a_i} is free, hence flat, over A_{a_i}.
Invert the product of the finitely many a_i. It is nonzero since A is a domain;
its basic open is nonempty and open in the original base. Every affine chart over
this basic open is flat, and flatness is local on the source, so the restricted
morphism is flat. For an empty inverse image the empty product is 1 and flatness
is vacuous. No Noetherian or finite-presentation hypothesis is used.

(blueprint: lem-sbc-generic-flatness) -/
theorem exists_nonempty_open_flat_restrict {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ Flat (f ∣_ U) := by sorry

end AlgebraicGeometry
