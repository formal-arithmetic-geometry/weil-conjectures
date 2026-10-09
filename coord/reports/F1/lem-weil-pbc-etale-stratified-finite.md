# F1 Delivery Report

Item: `lem-weil-pbc-etale-stratified-finite`

Files delivered:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-stratified-finite.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-separated-stratified-finite.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-affine-cover-gluing.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-stratification-local-gluing.json`

## Review by F1

I reviewed the split against Stacks Project Lemma 03S9 (the source proof at
`etale-cohomology.tex`, lines 12034-12061) and the cited DAG nodes. The item
statement matches 03S9: a quasi-compact, quasi-separated etale morphism is
finite etale after a finite constructible locally closed stratification of the
base, with the fibre product made explicit. The first proof step is exactly
the separated reduction through More on Morphisms Lemma 07RZ: etale gives
flat, locally finite presentation, and quasi-finite hypotheses; the resulting
finite locally free strata remain etale after base change and hence are finite
etale.

For the non-separated case, the second step follows 03S9 by taking the finite
affine cover supplied by `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`,
applying the separated node to every chart and overlap, and using
`lemma-constructible-common-refinement`. The new affine-cover-gluing node
records the omitted argument: finite etale overlap maps are proper, their
open inclusions into chart pieces are therefore closed as well as open, and
the affine gluing criterion gives separatedness of the union. The third step
applies the separated case to the resulting separated base changes. The
fourth step records the locality implicit in the source's phrase “we may
assume X is affine”; the new locality node now states this concretely: for a
finite affine open cover $X=\\bigcup_aW_a$, if each $W_a$ has a finite
constructible locally closed partition on whose pieces the base change of
$U$ is finite etale, then $X$ has such a partition. Its later split will
write the finite intersections and disjointization, using
`def-weil-constructible-subset` and `lemma-constructible-common-refinement`.

All three new structural nodes are intentionally `unsplit`, have statement-only
records, exact Stacks source places, and independent LeanSearch, Loogle, and
Mathlib-source grep searches showing that Mathlib has only the component
ingredients, not these scheme-theoretic stratification statements. Existing
definitions and tools are cited by node ID in `stmt_deps`/`uses`; no Lean code
was written or compiled.

Mechanical verification performed on the delivery branch:

- `python3 tools/review_split.py lem-weil-pbc-etale-stratified-finite` passes.
- `python3 tools/check_dag.py` reports zero cycles; its nine reach diagnostics
  are pre-existing repository warnings unrelated to this item.
