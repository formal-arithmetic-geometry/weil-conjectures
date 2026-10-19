# Q33 maintenance: derived dg quasifunctor invariance

The stage-2 retry loop was caused by missing statement dependencies. Before
repair the node listed only `def-weil-size-convention`, so `Dag.stage2()` offered
it although the existing dg-category, dg-module and coherent enriched
interfaces had no Lean binding or Mathlib match. Workers obeyed the bottom-up
brief by reporting `lem-coef-dgcat-model-structure` missing. Failure counters
and dispatcher notes were not the cause and have not been reset.

Maintenance added these existing interface owners to `stmt_deps` in the side
project and the authoritative live DAG:

- `lem-coef-dgcat-model-structure`: dg categories, dg functors,
  quasi-equivalences, cofibrant replacements and localization.
- `lem-coef-dg-module-projective-resolution`: modules, graded Hom complexes,
  homotopical projectivity and enhanced module localization.
- `lem-coef-dg-enrichment-rectification`: the derived enriched category and
  coherent localization interface used by enhanced equivalences.
- `lem-coef-enriched-category-tensor-calculus`: coherent enriched functor
  categories, composition, mapping objects and internal Hom.

All four already occur in `proof_deps`. The other two dg proof prerequisites,
`lem-coef-dgcat-bimodule-mapping-space` and
`lem-coef-dg-module-diagram-classification`, remain proof dependencies: their
classification theorems are used in the proof rather than needed as new
primitive interfaces. No statement, proof, review, search or Lean binding was
changed. The union of statement and proof edges is identical, and no added
statement dependency has a path back to the item. Existing files have adjacent
backups ending `.maint-Q33-dg-quasifunctor-1792162166.bak`.

The normal stage-2 queue and the dispatcher's existing recheck of held claims
now see the missing interfaces. This item resumes through normal bottom-up
eligibility after its prerequisites land. This is not a failure-count gate or
an abandonment. No Lean source changed; no compiler or global build is needed
for this metadata repair.

The next worker must read the repair note and the retained sandbox semantic
audit. Do not revive `scratchpad/earlier-attempt-20261016`: its arbitrary-`Prop`
law fields and untied functor data do not define the claimed dg structures or
derived invariance. Build on the prerequisite declarations when available,
then compile every delivered file separately within 60 seconds and run the
normal delivery preflight. Maintenance has not proved or formalized the item.
