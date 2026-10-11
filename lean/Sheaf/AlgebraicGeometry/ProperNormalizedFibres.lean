/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Connected fibres of a normalized proper morphism to an affine scheme

Source: Stacks Project, More on Morphisms, Theorem 37.53.5 (Tag 03H2), normalized
 affine reduction (blueprint: lem-weil-pbc-stein-normalized-fibre-idempotent).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Theorem 37.53.5 (Tag 03H2), normalized affine reduction.
(blueprint: lem-weil-pbc-stein-normalized-fibre-idempotent)
If the canonical map from the base ring to global sections is an isomorphism, every fibre
of a proper morphism is nonempty and connected; `ConnectedSpace` includes nonemptiness.

Proof: `lem-weil-pbc-stein-universally-closed-factor` identifies the relative spectrum of
 global sections with the base and makes the morphism surjective, giving nonempty fibres.
For connectedness, a nontrivial clopen decomposition gives a characteristic idempotent.
By `lem-weil-pbc-stein-fibre-idempotent-image`, it lifts to the stalk of the pushforward
structure sheaf. Properness gives quasi-compactness and quasi-separatedness by
`pqf-lem-proper-basic`, and `pqf-lem-pushforward-qcoh` gives quasi-coherence of the
pushforward. The universal factorization above, `lem-weil-pbc-affine-morphism-relative-spec`
and `lem-weil-pbc-affine-tilde-gamma-adjunction` identify that stalk with the local ring
of the base. The fibre map factors through its residue field (`def-pc-scheme-fibre`,
`def-weil-residue-field`). A lifted element is either a unit, whose idempotent image is 1,
or belongs to the maximal ideal, whose image is 0. Both contradict the characteristic
idempotent of `lem-weil-pbc-scheme-clopen-idempotent`. -/
theorem Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)] (s : Spec (.of R)) :
    ConnectedSpace (f.fiber s) := by
  sorry

end AlgebraicGeometry
