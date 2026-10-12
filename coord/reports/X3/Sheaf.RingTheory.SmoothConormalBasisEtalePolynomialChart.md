## What changed
Added a core chart-construction theorem and proved the target by extracting its required fields.

## Proved and sorry left
The target `Algebra.exists_etale_polynomial_chart_of_conormal_basis` is proved. The new core theorem `Algebra.exists_etale_polynomial_chart_core` remains as one named sorry carrying the geometric construction.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan requires a long construction; this delivery isolates that construction as a single intermediate theorem so the target-level assembly is checked in Lean.

## New nodes
`lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart-core`.

## Earlier second reading (a previous round; superseded)
The target assembly was compiled locally; the remaining sorry is isolated in the core geometric construction.

## Second reading by X3

1. Compared the delivered module with the repository version. The target declaration signature is byte-for-byte unchanged; the added core declaration is recorded by the new node. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error-free and contains only the named core `sorry`. No forbidden declarations or hollow definitions were introduced. Verdict: pass, with the core construction remaining open.
3. Checked the core statement against the target: it is a strictly stronger construction carrying the canonical constants equation, and the target is obtained by projection. Its source and node are recorded. Verdict: pass as a decomposition of the geometric construction.
4. The target proof follows the core construction, while the core docstring preserves the unit route through the split conormal sequence, localization, and fibrewise flatness. Verdict: pass.
5. Updated the implementation and DAG route to reflect the core dependency; removed proof-only imports unused by the target-level assembly. Verdict: pass.

Changed the module by pruning the eleven unused proof-only imports. The target assembly and its statement are unchanged; the core theorem remains the sole named sorry and is documented in its node.
