## What changed

Proved AlgebraicGeometry.ProEtale.closedEtaleTransport_bounds with its existing signature.
The proof constructs a natural isomorphism on all bounded constructible etale complexes,
then restricts it to the requested interval subcategory. It cancels the derived intrinsic
realization equivalence, uses the canonical unbounded comparison unit on bounded-below
objects, and identifies the two ordinary closed right adjoints by the proper
forget-supports comparison and uniqueness of right adjoints.

Private proved helpers obtain intrinsic etale origins, reflect intervals and Tor bounds,
and transport intrinsic constructibility, cohomological support and Tor amplitude along
isomorphisms. The final proof applies etaleClosedOutput_bounds separately to the
cohomological and Tor inputs. Every pro-etale module sheaf remains an allowed Tor test.
No statements, definitions, public imports or other modules were changed. The node proof,
proof dependencies and proof origin now record this implementation.

## Proved and sorry left

Closed one existing hole: AlgebraicGeometry.ProEtale.closedEtaleTransport_bounds
(lem-pur-closed-etale-transport-bounds). The module originally had one sorry and now has
zero. Added zero holes and no new public statements. All private helpers are proved.
This is a proof from existing declarations, not a decomposition into new holes.

Validation: server lcompile.py compiled the full module in 17.8 seconds with exit 0
and no warnings. A textual comparison confirms the existing theorem signature is
unchanged; all lines are at most 100 characters. Delivery preflight checks the
compiled declarations and their axiom reports.

## No longer needed

Removed direct private imports:
- Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
- Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
- Sheaf.Paper.ComparisonTorAmplitude
- Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude

Added proof imports of EtaleClosedOutputBounds, ComparisonTorInterval,
ProEtaleConstantModuleConstructibility, the source proper forget-supports comparison,
and the exact-derived equivalence API. FiniteRingConstructibleDerivedOrigin is retained.
All original public imports are retained. Removed the obsolete direct tool-use entries
lem-exc-closed-amplitude and prop-exc-closed-tor from the parent node; both remain
recorded under the retained etale closed-output dependency that actually applies them.

The declared dependency lem-pur-etale-witness-transport-data
(Sheaf.Paper.EtaleWitnessTransportData) is not imported: its fixed-scalar D+ witness and
transport constructions would require converting the intrinsic unbounded input back to
that presentation. Instead the already stated finite-ring origin theorem gives the
intrinsic witness directly, and the source unbounded comparison-unit theorem gives the
natural comparison directly. The retained comparison Tor interval theorem reflects
Tor for each witness without the additional invertibility setup of ComparisonTorAmplitude.

The lower closed-amplitude and closed-Tor statements are still used inside the retained
EtaleClosedOutputBounds dependency; they are not claimed globally unnecessary.
The generic site-comparison theorem is still mathematically used, through its existing
source unbounded canonical-unit form. No module is withdrawn and the unit route stays.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The two extracted proof dependencies
already compile with complete proofs in the current source. The fixed-scalar bounded-below
presentation of etaleWitnessTransportData does not directly match this intrinsic unbounded
statement, so the equivalent source unbounded unit and intrinsic finite-ring origin are
used directly. ComparisonTorInterval needs no additional prime invertibility assumption;
its existing hypotheses suffice for the Tor reflection in this proof.

The proof keeps r <= s and c >= 0, never imposes Tor on the cohomological branch,
and works for zero inputs, empty schemes, identity closed immersions, r = s and c = 0.
The isomorphism arguments preserve every test sheaf and use no arbitrary choice of data
from an unproved existence theorem.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
