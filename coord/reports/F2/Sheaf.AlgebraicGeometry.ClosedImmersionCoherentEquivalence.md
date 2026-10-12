## What changed

Proved `closedImmersion_coherent_equivalence` by restricting pushforward to coherent modules, using
finite pushforward coherence, ideal annihilation, full faithfulness, and the annihilated-module
pullback unit. Proved `closedImmersion_coherent_support` from the closed-immersion stalk theorem.
Added a private `product_zero_iff` helper to identify ideal-product vanishing with sectionwise
annihilation. The namespace/import visibility change is recorded in
`coord/changes/ClosedImmersionCoherentEquivalence-imports.md`.

## Proved and sorry left

Closed `closedImmersion_coherent_equivalence` and `closedImmersion_coherent_support`.
The existing named hole `closedImmersion_coherentFormal_equivalence` remains, with its existing
blueprint node `lem-weil-pbc-closed-immersion-coherent-equivalence`.

## No longer needed

No imports were removed. The proof uses the existing pushforward annihilation, full faithfulness,
finite pushforward coherence, coherent finite-type criterion, closed pushforward stalks, and
coherent formal module imports.

## Where the brief, the DAG or earlier work was wrong

The DAG route is valid. The formal-system equivalence is considerably longer than the two preceding
components and remains for a subsequent worker.

## Earlier second reading (a previous round; superseded)

The two completed proofs preserve the declared statements. The remaining formal-module theorem is
unchanged and remains attached to the existing blueprint node.

## Second reading by F2

1. The delivered module was diffed against the repository version. Existing declaration
   signatures are unchanged; the proof-only TensorSection import and namespace openings are
   covered by `coord/changes/ClosedImmersionCoherentEquivalence-imports.md`.
2. The module compiles with `lcompile.py`; the two completed declarations contain no `sorry`,
   and no forbidden declarations or hollow definitions were introduced. The remaining
   `closedImmersion_coherentFormal_equivalence` hole is the pre-existing named theorem.
3. No new split-off statement was added. The private `product_zero_iff` helper is local to the
   proof and duplicates no library declaration; the existing searches and source dependencies
   were checked.
4. The proof follows the unit route: finite pushforward coherence, ideal annihilation,
   full faithfulness, essential surjectivity via tensor pullback, and the closed-pushforward
   stalk calculation. The proof-only import is required; no import can be pruned.
5. The declarations prove the node statements exactly as written. The DAG node and its
   proof dependencies remain applicable, with the formal-system component intentionally open.

Changed during second reading: no source or proof changes; this report section records the
checks above.
