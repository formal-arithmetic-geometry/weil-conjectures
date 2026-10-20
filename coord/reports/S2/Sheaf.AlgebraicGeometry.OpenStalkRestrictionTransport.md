## What changed

Retired the assigned duplicate Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport.
The source twin already proves the transport law for the canonical comparison family,
with the additional identity-component property for restriction composition.
The transport node now points to that existing source theorem, recording its exact signature.

Adapted the only remaining direct consumer, Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift:
replace its private transport import, choose openModuleStalkRestrictionComparison as e,
and discard the source theorem's extra identity-component clause. Its existing public
signature, visibility, attributes and public imports are unchanged.
Change record: coord/changes/S2-retire-open-stalk-restriction-transport.md.

## Proved and sorry left

This is a zero-hole retirement, not a new proof or decomposition.
Holes closed: none (0 of 0). Holes added: none (0). Split off: none (0).
No sorry remains in the adapted consumer or the withdrawn module. The existing proved
source theorem AlgebraicGeometry.Scheme.exists_openStalk_restriction_transport realizes
lem-sc-open-stalk-restriction-transport; its private descent and adjunction proofs remain
in the source library unchanged.

The adapted consumer compiled with lcompile.py in 4.4 seconds with no warnings.
The dry run additionally checks axioms and the delivery preflight. The fixed family
is chosen before m, N or t, so the consumer's original quantifier order is preserved.
The argument includes equal opens and rank zero; x in W excludes an empty neighbourhood.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport, including its
three duplicate private helpers and its existential wrapper of the source theorem.
Removed its private import from Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift,
replacing it with WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport.
No other import is removed. No mathematical node or dependency edge is pruned: existing
DAG parents now obtain the same transport assertion from the source realization.
The unit's statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an obligation already proved by an earlier worker.
The current queue explicitly assigns retirement. The inventory lists two consumers,
but OpenStalkFreeMapOneLift has already been retired, leaving one direct Sheaf importer.
No quarantine importer was found. The source theorem has a stronger API: its family
is canonical and c has identity components, while the Sheaf theorem existentially
packages the family and states only the transport law.

An import-only migration was checked and failed at the old obtain of e and he:
Tactic rcases failed because the source theorem is universally quantified over V,
not an inductive existential package. The adapted proof supplies the explicit family
and unpacks the extra conjunction; these are the necessary consumer changes.
The source's adjunction-descent proof follows the recorded DAG plan, and all
mathematical dependency edges remain needed and attached to existing declarations.

Real msearch.py searches with leanfinder, loogle and grep found Mathlib's additive
restrictStalkNatIso and its germ formulas, restriction adjunction and fully faithful
pushforward. Direct rg inspection found the fully proved stronger source transport
theorem. The source proof and the local consumer's categorical cancellation calculation
were read before migration; no theorem statement is weakened or admitted.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
