# Q58 returned stage-2 dependency repair (2026-10-21)

Return L for immutable head 9e7a2d8e17ee explicitly requires
lem-weil-pbc-ringed-strict-tower-projection-morphism in the item's proof_deps,
while def-sbc-strict-projection-tower-data owns the existing plain definitions
used in the statement and the two new strict coefficient definition nodes.
F2 additionally requires the missing def-sbc-quotient-coefficient-presentation
node record. Both definition-ownership repairs are saved in Q58's packet.

The authoritative item omitted the required theorem from proof_deps. The
delivery wrapper accepts that additive repair, but node_fields.py and
stage2_delivery.py classify it as a statement correction and reject it with
the unchanged mathematical statement. This deterministic ownership mismatch
caused the repeated repair failures after successful single-file compiles.

Maintenance applies L's required citation to the authoritative node on
sheaf-dag, also adding it to step 5's uses (the existing augmented projection
naturality compatibility), so proof_deps stays the union of uses. All seven
proof texts, the statement, statement dependencies, Lean records and source
files are preserved. No mathematical proof or statement correction is added.
The old field refusal is reproduced; changed-node graph checks and review_split
pass before this commit. No launcher, review, preflight or landing tool changed.

Next worker: refresh the base using deliver2.py, retain all six node records
and five Lean modules, compile one file at a time, and rerun the usual dry run
and delivery. Preserve the corrected main proof annotations when refreshing
the item. The wrapper preserves them over a stale sandbox proof field. Do not
invent statement_change or drop the required theorem dependency. The pending
packet remains subject to the ordinary independent maintainer review.

Backup (untracked):
dag/nodes/sec-smooth-base-change/lem-sbc-strict-quotient-exchange-unit-equation.json.maint-Q58-1792571278.bak
