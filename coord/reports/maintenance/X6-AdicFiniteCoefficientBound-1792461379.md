# Maintenance: X6 Sheaf.WeilSheaf.AdicFiniteCoefficientBound (2026-10-20)

The repeated deterministic failure is a brief/packet error. The adopted-source
policy in tools/stage3_gate.py predates this packet: existing declarations in
lean/WeilConjectures/ stay verbatim. The broad unclaimed-module/pruning permissions
in the worker briefs omitted that boundary. The worker therefore removed
AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant from
WeilConjectures.WeilSheaf.PoincareDuality and concluded that the gate was broken.
It is a protected upstream declaration, present when the source tree was adopted
(commit 7932860b3a); it is not an approved false-statement correction. The gate
correctly refuses this packet. A module being unclaimed does not waive the rule.

coord/brief-stage3.md, stages/3-proving-and-pruning.md and the dispatcher's
briefs/batch1/stage3-worker.md now state the boundary explicitly. No delivery,
gate, landing, review, provider, admission or dispatcher code was changed.

For the next worker:

1. The retained pruning packet is historical work, not an authorized delivery.
   Do not repeat it unchanged expecting a gate change. Keep its useful proof work.
2. Preserve PoincareDuality.subsingleton_cohomology_adicConstant with its original
   signature and a complete proof. Either find a shorter proof preserving that
   declaration and eliminating its bound dependency, or restore and prove
   Sheaf.WeilSheaf.AdicFiniteCoefficientBound. Do not replace the proved upstream
   helper by sorry. The maintenance engineer did not undertake either proof.
3. If restoring the item: copy its current server module back into the sandbox;
   remove its entry from deleted.txt; restore the affected sandbox node records
   from current sources (in particular the bound node's lean attachment); update
   or remove the obsolete pruning change record and rewrite report.md to describe
   the actual new delivery. Check all retained adaptations against current sources.
4. Follow the normal 60-second single-file compile and delivery checks for the
   repaired packet. A baseline containing the existing sorry is not proof progress.

Evidence: the most recent completed attempt before maintenance was
1792456407, with one preflight refusal for the removed declaration. The dispatcher
had tries=10 and the same note. Earlier provider HTTP 429 interruptions, including
the prior maintenance run, are provider failures, outside this repair; they were
not addressed with any provider/admission/concurrency change. No provider error
occurred in this maintenance session.

The full pruning packet was archived on the maintenance machine as
evidence/retained-pruning-packet.bak.tar.gz. All existing edited files have
.maint-X6-1792461379.bak backups. The live worker's Lean and DAG files were left
untouched because attempt 1792461386 was already running.
