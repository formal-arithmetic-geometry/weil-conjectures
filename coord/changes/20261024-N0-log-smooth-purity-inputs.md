# N0: reopen the exact log-smooth purity inputs, 2026-10-24

Q84 reopened `lem-per-log-smooth-trait-punctual-purity` without its old proof, but retained exclusions on its
three exact direct inputs. Eleven worker attempts reached the same route contradiction;
dry runs correctly reject the unchanged unsplit packet. This is a route-data defect,
not a theorem counterexample, provider failure or delivery permission failure.

This maintenance decision extends `coord/changes/20261024-Q84-gabber-purity-inputs.md`
only for these existing finite-coefficient interfaces:

- lem-per-regular-log-smooth-monomial-chart
- lem-per-monomial-trait-punctual-purity
- lem-per-punctual-purity-etale-locality

They are admitted as UNSPLIT stage-1 work. Preserve every statement, source,
statement dependency, search and blueprint field. Withdraw the old proofs,
proof dependencies, proof origins, split reports, reviews, tool-use approvals
and theorem Lean attachments. Released repair notes use keep_plan=false and
require fresh reconstruction and independent review. The item's own mathematics
is left to its worker; it may cite these admitted unsplit interfaces now.

The statement-dependency closure contains 246 nodes and has no other exclusion.
The old full proof closure has 73 excluded nodes; it is not reinstated.
With the three proofs withdrawn and the exact exclusions removed, their full
remaining closure has 10442 nodes and no excluded node. No duplicate node is created.

Remove only the two exclusive stale module exclusions:

- Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity
- Sheaf.AlgebraicGeometry.PunctualPurityEtaleLocality

Those modules remain absent. The existing shared
`Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart` module is already outside
the module exclusion list and stays byte-for-byte unchanged. Its definition owner
`def-per-monomial-trait-model` retains its attachment; the module's chart theorem
contains sorry and is not a proof. Do not delete this shared definition module or
mistake the theorem's old record for approval of the withdrawn split.

The Q84 decision remains historical; its unlisted-exclusion sentence is superseded
only for the three ids and two module exclusions above. All other exclusions,
the 2026-10-19 pivot, no-SGA rule and prohibition on arbitrary-field adic duality
and the discarded Artin-Gabber route remain in force. No existing theorem is weakened.

The repair note, N0 return and preferred-upstream brief explicitly supersede the
stale blocker, preserving the worker's sandbox, searches and source assembly.
No Lean source, protected launcher/review/landing tool, queue, claim, failure counter
or concurrency setting is changed. Pre-repair checkpoint: 5a09bf1113ac43827d1f26e983e1e4c80e113c3b.
Each changed/new file has a sibling `.maint-N0-log-smooth-20261024.bak` (empty for a new file).
Audit: `coord/maintenance/20261024-N0-log-smooth-purity-audit.json`. Commit under the server merge lock with Bin Wu's identity.

## Q91 monomial source interface extension, 2026-10-24

The unlisted-exclusion restriction above is superseded only for the six existing interfaces and six exclusively owned deleted module ids listed in coord/changes/20261024-Q91-monomial-purity-inputs.md. They are admitted as UNSPLIT stage-1 work, with old proofs and approvals withdrawn. Every other exclusion and source restriction remains; the historical proof closure is not reinstated.
