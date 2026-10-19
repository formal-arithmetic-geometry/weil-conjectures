# Q111: lem-a1-subquotient-extension-bounds

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-subquotient-extension-bounds.json`: existing item, retained statement and hypotheses, now split in three proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node in every proof step.
- `report.md`: this review and delivery report. No Lean files, compiler, Lake, or build tools were used.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and the shared `lean/WeilConjectures/` for the blueprint tag, the item name, and Frobenius mixed/subquotient declarations. The source contains eigenvalue-bound declarations for injective and surjective Frobenius maps, but they define `HasWeightsAtMost` by an eigenvalue inequality and do not state this item's mixed-filtration proposition. No exact finished declaration is attached.

## Literature wanted

WANTED: None. The blueprint proof is available in `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/lem-a1-subquotient-extension-bounds.proof.md`; the split follows it and expands the linear-algebra details.

## Corrections and retained work

The inherited statement is mathematically valid and unchanged. The imported proof was too compressed: it asserted that submodules and quotients are mixed after observing eigenvalue containment, without constructing the required mixed filtration. I repaired this by first bounding all ambient eigenvalues using the determinant factorization along the given mixed filtration, then transferring the bound to a stable subquotient, and finally constructing an invariant composition filtration of that subquotient. Since the coefficient field is algebraically closed, each one-dimensional factor has a scalar Frobenius and receives its real weight from its eigenvalue modulus. The inequality gives that weight at most `w` because the fixed prime power satisfies `q > 1`.

The existing `p-linear-filtration` node is the exact cited tool: its statement supplies both the determinant product along a filtration and the fact that a subquotient's eigenvalues occur in the ambient spectrum. I removed the imported citation to `lem-a1-spectrum-exact-sequence`, because it is redundant and its exact-sequence hypothesis is not needed. The definition node supplies the meaning of mixedness, stable filtration, and pure graded quotients. No statement dispute, duplicate, route replacement, SGA citation, or new auxiliary node arose.

## Not duplicates

There are no new nodes. The whole DAG and both blueprint snapshots were searched for pure/subquotient Frobenius bounds. `lem-a1-subquotient-pure` concerns irreducible lisse Weil sheaf subquotients and is not a statement about finite Frobenius modules or mixed filtrations; `lem-a1-mixed-direct-summand` is a sheaf-level closure result that cites this item. The existing `p-linear-filtration` is strictly more general linear algebra and is cited rather than duplicated.

## Mathlib searches

For the item I ran the required `msearch.py` searches and retained their exact queries and outputs in `searches.jsonl`: LeanFinder returned only Lie-module weight-space declarations; Loogle returned no hits and reported the project namespace as unknown; grep found no matching declarations; LeanSearch returned ideal/module filtration APIs unrelated to Frobenius weights. These are recorded in the item's `mathlib_searches` with the unavailable Loogle verdict. No Mathlib leaf is claimed.

## Review by Q111

I read the item, `coord/brief-stage1.md`, stages/1-dag.md, AGENTS.md, SETUP, GOAL, dag-sync, the chapter `sec-deligne-laumon-a1`, and unit `sk-l-dl-a1-endpoints`. I read both the master and main-20261015 blueprint statement/proof. I also opened the complete statements of `def-weil-frobenius-module-weights` and `p-linear-filtration`, plus the related `lem-a1-spectrum-exact-sequence` and the downstream sheaf nodes to check for duplicates and route use.

Step 1 uses the definition's actual mixed filtration and pure graded-piece clauses. It applies the displayed determinant factorization from `p-linear-filtration` successively, so the ambient spectrum is the union of the graded spectra; the weight inequalities then give the ambient bound. The empty module is explicitly covered.

Step 2 uses exactly the p-linear-filtration statement that eigenvalues on any stable subquotient occur among those of the ambient module. The quotient action is well-defined because the quotient subspace is Frobenius-stable, which is part of the item's subquotient hypothesis. No conclusion is taken from the proof of a cited node.

Step 3 checks the algebraically closed coefficient field and finite dimension from the Frobenius-module setting, then constructs a composition filtration by repeatedly choosing an eigenvector and passing to the stable quotient. Each one-dimensional factor is pure at the real weight determined by its eigenvalue modulus, and the logarithmic inequality gives that weight at most `w`; this is exactly the filtered criterion in the definition. The zero quotient case is vacuous. Applying the construction to a stable submodule, quotient, or their combination gives the claimed subquotient result.

For the B--E checklist, every non-elementary fact used in the steps is supplied by a cited node or written out as the finite-dimensional linear-algebra argument. Every citation has a verbatim quote in `citations.json`; all cited nodes were opened and say what the steps take from them. There are no new nodes to duplicate, no cycles, no hidden clause-node, no source error, and no step over 2000 characters. Edge cases checked: `V=0` with empty filtration; a one-dimensional scalar module; a non-semisimple Jordan block; a stable eigenline quotient; and a two-step diagonal module with weights below and at the bound. The proof does not assume semisimplicity or a Frobenius-stable complement.

## Unfinished work

None in the split. The mandatory server dry run and delivery remain to be run on this sandbox.
