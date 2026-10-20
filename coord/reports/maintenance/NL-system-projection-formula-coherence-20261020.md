# Maintenance: NL strict-system projection-formula coherence

Item: lem-pur-system-level-projection-formula-coherence, stage 2.
Returned delivery: ec9ccd68059b. Maintenance run: NL-1792501354, 2026-10-20.

The retry history has two distinct causes. Before the 10:47 UTC upstream-sync
quarantine, the repaired packet compiled but failed stage-2 preflight.
The return of 03:07 UTC explicitly requires the two theorem nodes to remain
proof dependencies while definition nodes own the statement's helper definitions.
The worker therefore added lem-coef-finite-free-extension to proof_deps.
The launcher deliver2.py accepts that additive repair; the server's
tools/node_fields.py/check_statement_change classifies it as a mathematical
statement correction and tools/stage2_delivery.py demands a correction report.
The statement and proof text are unchanged.

Maintenance records that already requested citation in the live node's
proof_deps, the maintainer-owned base data for the returned stage-2 packet.
This is the sole changed node field: one dependency added, none removed.
The statement, proof, existing Lean binding and review records are preserved.
An in-memory call to the unchanged check_statement_change reproduces the old
refusal; comparison to the corrected base has no correction fields or errors.
No statement_change has been invented, and no validation gate was disabled.

Later attempts fail before preflight. Sync 5f7b33eac at 10:47:43 UTC moved
Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses and its importers to
quarantine/. The recorded error is a duplicate
CategoryTheory.ringedSiteZerothHypercohomology imported from both the Sheaf and
WeilConjectures modules. All three direct Sheaf imports of the NL packet are
in coord/rework.tsv: SystemCompactificationProjectionSubstitution,
CoefDerivedSystemEvaluationCalculus and FiniteFreeCoefficientExtension.
Thus --source correctly finds no live source; this is not a permission error
or a reason to weaken or rewrite the item's mathematics.

X2 has already delivered the canonical-import repair at 68becc60fe on
deliver/X2/Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses. That packet
replaces the duplicated small-site definition by a public re-export of the
identical upstream definition and restores the unchanged theorem from quarantine.
Its report records successful per-file checks and unchanged consumers.
It had not landed when this report was written. Maintenance did not overwrite
that pending delivery or copy quarantined modules into the live library.

Next worker: retain the repaired four-import module, the existing-definition
ownership records and clause-by-clause reading. Refresh the live base so this
proof_deps addition is no longer a packet/base difference. Full compilation
still requires normal landing and rework restoration of the quarantined imports.
The final local REPORT.md records exact validation and follow-up details.

Protected launcher and landing tools are not changed. In particular the
general inconsistency between deliver2.py and node_fields.py/stage2_delivery.py,
and repair dispatch ignoring the live rework dependency state, require changes
by their owner. No provider error was identified, no process was killed, and
no scheduling limit or pause was introduced.
