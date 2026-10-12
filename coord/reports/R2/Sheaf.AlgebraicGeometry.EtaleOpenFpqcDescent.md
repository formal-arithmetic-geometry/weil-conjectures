## What changed

Proved `AlgebraicGeometry.existsUnique_open_of_etale_fpqc_baseChange` by applying
`openSubscheme_existsUnique_of_fpqc` to the base changed family. The fpqc covering
hypothesis is transported with `Precoverage.pullbackArrows_mem` and
`Presieve.ofArrows_pullback`; the given compatibility is exactly the compatibility
required by the general descent theorem. No imports were added or removed.

## Proved and sorry left

The declaration `AlgebraicGeometry.existsUnique_open_of_etale_fpqc_baseChange` is
proved. No `sorry`s remain in the delivered module.

## No longer needed

None. The proof uses the stated descent dependencies: `lem-galois-fpqc-covering-base-change`
through `Precoverage.pullbackArrows_mem` and
`lem-weil-pbc-open-subscheme-fpqc-descent` through
`openSubscheme_existsUnique_of_fpqc`. The fibre-product dependency
`def-pc-fibre-product` remains in the pullback objects and overlap maps.

## Where the brief, the DAG or earlier work was wrong

The old node proof called the projections from `T_i ×[S] V` to `V` first
projections; they are second projections. Corrected this wording in the node.


## Second reading by R2

1. **Unchanged public statements — pass.** Diffed the only delivered module against
   the repository: only the original theorem's proof body changed. Its signature,
   existing docstring, definitions and imports are byte for byte unchanged. No new
   declaration or change record is present.
2. **Proof and trust — pass as a reduction to an open dependency.** Compiled the
   module locally without errors or warnings. It contains no `sorry`, axiom,
   unsafe/opaque declaration or foreign implementation. A scratch copy with
   `#print axioms AlgebraicGeometry.existsUnique_open_of_etale_fpqc_baseChange`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter comes from the imported, still-open
   `AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`; this delivery closes
   the item's proof body, not that general theorem's proof.
3. **Split statements — pass, none.** No new theorem, split-off statement, hollow
   definition or new node was introduced. The imported theorem is the pre-existing
   general compatible-open descent theorem, strictly broader than this base-change
   reduction. Empty covering families force the base to be empty; empty/all opens
   and singleton covers remain valid, and no extra nonemptiness is assumed.
4. **Route and pruning — pass.** Read the Mathlib implementations of
   `Precoverage.pullbackArrows_mem` and `Presieve.ofArrows_pullback`, searched the
   upstream and Sheaf algebraic-geometry sources for open descent, and inspected
   Mathlib's flat-descent results (properties of morphisms, not compatible opens
   for an arbitrary covering family). The existing two-step reduction is direct.
   Both public Mathlib imports supply signature notions; the Sheaf import is
   correctly proof-only. No imports or old proof dependencies are unused. Read
   `dag/units/sk-thm-iff.json`; its realization and unit route are preserved.
5. **Node agreement — pass after wording repair.** Kept the three proof dependencies
   and the document proof origin. Made the proof steps name the actual Mathlib
   transport lemmas and explain that Lean's overlap hypothesis already matches
   general descent, with no explicit associativity transport needed.

Changed only the node's proof wording and this report. The Lean proof needed no repair.
