/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Connectedness of the generic fibre of a flat degeneration

Source: Stacks Project, Tag 055J.
-/

@[expose] public section

universe u
open CategoryTheory IsLocalRing
namespace AlgebraicGeometry

/-- A connected flat scheme over a DVR with reduced closed fibre has connected generic fibre.

Source: Stacks Project, Tag 055J.
Proof: Write π for a uniformizer. If the generic fibre were disconnected, its structure
sheaf would have a nontrivial idempotent e. On an affine open Spec A of the total space,
flatness makes π a nonzerodivisor, and the generic fibre has coordinate ring A[1/π].
Write the restriction of e as z/π^n with n minimal. The equation e² = e gives
z² = π^n z in A by flatness. If n were positive, z modulo π would be nilpotent in
A/πA. Reducedness of the closed fibre implies z is divisible by π, contradicting
minimality. Thus e extends to A. These extensions are unique because π is a
nonzerodivisor; they agree on overlaps and glue to a global idempotent. Connectedness
of the total space forces that idempotent to be zero or one, contradicting the choice
of e. Flatness and nonemptiness of the total space ensure the generic fibre is nonempty:
every nonzero flat R-algebra embeds into its localization at π.
(blueprint: lem-sbc-connected-generic-fibre-trait) -/
theorem connectedSpace_generic_fibre_of_flat_trait {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [ConnectedSpace X] [IsReduced (f.fiber (closedPoint R))] :
    ConnectedSpace (f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) := by sorry

end AlgebraicGeometry
