# Q42 maintenance: hyperdescent coefficient statement dependencies

The stage-2 retries came from omitted statement dependencies. The item uses the
enhanced derived category of module complexes, but its four recorded inputs
provided only the ordinary Mathlib derived category, size conventions, generic
enhanced diagrams/cones, and set-sheafification. They did not construct the
enhanced module coefficient category and its mapping/cohomology interpretation.

The existing foundation nodes are:

- `lem-coef-enhanced-localization-universal`;
- `lem-coef-dg-model-mapping-comparison`;
- `lem-coef-projective-cochain-monoidal-model`.

All three were split/reviewed but had no Lean binding or Mathlib match at
diagnosis. The sibling `lem-cbc-grothendieck-coherent-end` already identifies
the latter two as the presentation of the same coefficient category. The
generic enhanced-localization predicate in `Sheaf.Paper.SheafFlatModel` and
its construction for module sheaves do not supply this recorded module-complex
coefficient interface. An ordinary derived-category nerve loses higher mapping
data and is not a substitute.

The workers followed the current bottom-up instruction correctly. The node's
missing edges let both the queue and the held-claim readiness check accept the
item prematurely. The dispatcher's runtime wait handler is disabled, so repeated
BLOCKED answers alone did not repair the graph. Delivery-log entries from NS
and Q05 are reviewed stage-1 splits, not stage-2 Lean statement landings. The
first Q42 READY answer likewise described stage-1 work and had no Lean payload.

Maintenance adds the three existing nodes to `stmt_deps` and inserts their
citations at the existing enhanced-derived-category clause. No mathematical
assertion, hypothesis, conclusion, proof step, proof dependency, or Lean binding
is changed. The authoritative node under `~/weil-conjectures-sheaf` and its
mirror under `~/weil-newtargets` are both repaired, under their own merge locks;
a side-only edit would be overwritten by `tools/sync_newtargets.py`.

Existing modified files have sibling backups ending in
`.maint-Q42-hyperdescent-1792181805.bak`. The side queue/index is regenerated
after backup. No failure counter, dispatcher code, claim, or Lean source is
changed. No worker is stopped and no global build is run.

The next worker should use the actual published coefficient foundation
declarations after their statement dependency chain is grounded. Do not state
those other DAG nodes in this consumer's delivery, restore the discarded
placeholder draft, or infer READY from compilation of the scratch interface
probe. The repaired node will become eligible through the existing bottom-up
queue and held-claim checks once its genuine prerequisites land. Failure counts
remain historical counts and impose no dispatch restriction.

At diagnosis the ready statement frontier below the three prerequisites was
`def-coef-infinity-fibrations`; other paths still require their own stage-1
work. These are normal prerequisite tasks, not mathematics to fold into this
consumer. Re-read the live declarations when the consumer is offered again.
