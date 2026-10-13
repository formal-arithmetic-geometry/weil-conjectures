## What changed
Proved `horizontal_ordinary_forward_fixed_pasting` by introducing its supplied comparisons and equality hypotheses, substituting the canonical comparisons, and applying `horizontal_ordinary_forward_fixed_pasting_core`.

## Proved and sorry left
Proved: `horizontal_ordinary_forward_fixed_pasting`. Sorry left: `horizontal_ordinary_forward_fixed_pasting_core` (node `lem-sc-horizontal-ordinary-forward-fixed-pasting-core`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG plan omitted an explicit Lean intermediate statement for the fixed-comparison mate calculation; it is recorded as the new core node.

## New nodes
`lem-sc-horizontal-ordinary-forward-fixed-pasting-core` records the remaining fixed-comparison mate calculation.

## Earlier second reading (a previous round; superseded)
The reduction substitutes exactly the supplied equalities and leaves the canonical fixed-comparison identity as the strictly simpler open node; signatures and the unit route are unchanged.

## Second reading by S2
1. Compared the delivered module with the repository version. Existing declaration signatures are byte-for-byte unchanged; the only existing proof change is the substitution proof of `horizontal_ordinary_forward_fixed_pasting`. Verdict: pass.
2. Compiled the module with `lcompile.py`. There are no errors, forbidden declarations, or unexpected `sorry`s; the sole remaining `sorry` is the named core theorem reported above. Verdict: pass, with the core intentionally split off.
3. Checked the split-off core statement against the displayed canonical component identity and its node. It is a strictly simpler fixed-comparison statement, with the Stacks source and a complete mate-calculation proof sketch; it does not restate the supplied-comparison target. Verdict: pass.
4. Checked the proof route and imports. The target proof eliminates the supplied equalities and invokes exactly the core node; the canonical definitions and the unit's horizontal route remain in place. No unused import or old proof dependency was identified. Verdict: pass.
5. Checked DAG consistency and edge cases. The node's Lean declaration, `proof`, `proof_deps`, `proof_origin`, module, and unit agree with the delivered file; identity, empty, and zero cases require no extra hypotheses by the stated categorical argument. Verdict: pass.

Changed only the target proof/docstrings and added the named core theorem/node; no statements or definitions were altered.
