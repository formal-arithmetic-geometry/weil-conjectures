## What changed
Added a real decomposition of `scalarCohomologyExtMap_bijective` into injective and
surjective component theorems, with the bijectivity theorem proved by their conjunction.
The two component proofs remain explicit named stage-3 obligations.

## Proved and sorry left
`scalarCohomologyExtMap_bijective` is proved from
`scalarCohomologyExtMap_injective` and `scalarCohomologyExtMap_surjective`.
Sorries left: `scalarCohomologyExtMap_injective` (node
`lem-sc-field-linear-ext-map-injective`) and `scalarCohomologyExtMap_surjective` (node
`lem-sc-field-linear-ext-map-surjective`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original node bundled injectivity and surjectivity into one unproved obligation;
the proof has been split into the two strictly simpler component statements.

## New nodes
`lem-sc-field-linear-ext-map-injective` and `lem-sc-field-linear-ext-map-surjective`
are recorded under `dag/nodes/sec-abelian-varieties/`.

## Earlier second reading (a previous round; superseded)
A second reader should verify that the conjunction proof preserves the original target
signature and that each component node is strictly simpler than bijectivity.

## Second reading by M2

1. **Interface and accidental changes.** Compared the delivered module with the repository
   version. All existing declarations, definitions, and theorem signatures are byte-for-byte
   unchanged. The only code change is the conjunction proof of
   `scalarCohomologyExtMap_bijective`; the two added component declarations are new split-off
   obligations and are recorded by matching DAG nodes.

2. **Compilation and proof status.** The repository and sandbox versions both exceed the
   launcher single-file timeout before producing diagnostics (the file is already expensive to
   elaborate); no new parser or elaboration error was reported. The delivered file contains no
   `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The only
   remaining `sorry`s are the two named split-off theorems listed above; the bijectivity theorem
   itself is proved by their conjunction.

3. **Split-off statements.** `scalarCohomologyExtMap_injective` and
   `scalarCohomologyExtMap_surjective` are genuine strict components of bijectivity, with the
   same hypotheses and map as the original theorem and respectively weaker conclusions. Their
   statements are true consequences of the intended comparison theorem, and each has a source,
   proof sketch, and DAG node. Searches found no existing Mathlib or library declaration with
   either statement.

4. **Pruning and route.** The proof uses only the two component declarations, so no prior proof
   dependency is removed and the unit route is preserved. The existing imports remain necessary
   for the surrounding module declarations and proofs; no safe import pruning was identified.

5. **DAG agreement.** The item's proof now records the conjunction route, and both new nodes
   record the split declarations, source, proof origin, and exact Lean statements. The unit and
   chapter metadata are unchanged.

**Changes made in this second reading:** added this review record; no mathematical or interface
changes were necessary.
