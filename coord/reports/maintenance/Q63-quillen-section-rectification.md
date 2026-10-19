# Q63 maintenance: Quillen-section rectification

The repeated stage-2 BLOCKED results came from an omitted statement dependency.
The item listed only `def-weil-abstract-derived-category`, although its enhanced
localization and coherent mapping-complex conclusion needs the coherent
enrichment notion owned by the existing `def-coef-complete-algebroid` node.
That definition is reviewed and split, but has no Lean binding or Mathlib match.
A stage-1 delivery is not a stage-2 declaration. The bottom-up brief correctly
forbids a worker from stating another existing DAG node in this delivery.

The omitted edge made the queue and the dispatcher's held-claim readiness check
accept an item without its definitions. Failure counts were not the cause.
Maintenance appended `def-coef-complete-algebroid` to `stmt_deps`, preserving all
other fields, in both server repositories:

- Authoritative `/home/ubuntu/weil-conjectures-sheaf`: commit
  `dc4879c80b80c97e0d95b41db2b5661764993188`.
- Side `/home/ubuntu/weil-newtargets`: commit
  `142e4395e4fb1be3713d15beba622312af022306`.

The repaired relative path in each is
`dag/nodes/sec-six-functors/lem-coef-quillen-section-rectification.json`.
Both originals have adjacent `.maint-Q63-1792176828.bak` backups. Commits were
made under each server merge lock as `Bin Wu <844524296@qq.com>`, with
`SHEAF_LEAD=L-only`, committing only the named node. The live repair is required
because `coord/sheaf.env` points `SHEAF_DAG` at the authoritative live DAG, and
the side synchronizer imports committed live records.

The added definition has no path back to the consumer through statement, proof,
step-use or merge edges. Queue validation compares the backed-up node with the
repair using the configured server graph. The theorem's proof dependencies are
not promoted to statement dependencies merely because they are unstated. No
mathematics, Lean source, compiler limits or failure counters were changed.

## Draft observed during maintenance

The attempt started at `1792176830` wrote
`lean/Sheaf/CategoryTheory/QuillenSectionRectification.lean` in the Q63 sandbox.
It is not a valid formalization candidate: `DgModelCategory` has fields such as
`locallyPresentable : Prop`, `enrichedOverComplexes : Prop`, and
`modelClassesAndAxioms : Prop`, with neither actual structure nor proofs of
specified properties. Its purported adjoints are functions between object
types. `StrictSection.transition` is a function out of an object rather than a
categorical morphism. The conclusion likewise chooses arbitrary propositions
called `mappingComplexes`, `freeEvaluationFormula`, and so on. Choosing all those
propositions to be `True` does not express the theorem's mathematical clauses.
A successful compile would not establish statement fidelity.

Do not deliver, bind, or resume that draft as a valid statement. Maintenance
preserved a snapshot at
`/home/ubuntu/weil-launcher-all/maint/Q63-lem-coef-quillen-section-rectification-1792176828/evidence/QuillenSectionRectification.lean.bak`
and the contemporaneous worker report beside it. Worker prompts and logs remain
under `/home/ubuntu/weil-launcher-all/run/Q63/lem-coef-quillen-section-rectification.*/`.
No valid Lean binding or completed stage-2 delivery existed when the repair was
installed. Maintenance did not modify the active worker's sandbox or kill it.

## Next worker

Read the current shared node after its recorded statement prerequisites have
landed. Refresh any sandbox node copy so it retains the repaired `stmt_deps`.
Use the actual complete-algebroid interface; do not duplicate that existing
definition or use arbitrary propositions as a substitute. The prerequisite's
own foundational nodes must be handled by the normal bottom-up pipeline.

Preserve the arbitrary small index category, genuine dg model structures and
Quillen adjunctions, coherent unit/composition data, projective section model,
free evaluation coproduct, derived totalization over every composable string,
composition preservation, and componentwise equivalence detection. Retain the
empty, discrete, identity-only, and nontrivial-endomorphism index cases. Compile
eventual Lean modules one at a time with the prescribed 60-second wrapper, then
run the normal delivery dry run and independent statement review.
