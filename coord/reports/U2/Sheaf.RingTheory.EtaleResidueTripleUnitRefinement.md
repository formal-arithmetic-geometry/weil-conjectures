## What changed

Replaced the sole sorry in `Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`
with the principal-localization construction described by its existing DAG node.
The proof constructs `Localization.Away f`, extends the map to K, takes its kernel
prime, and constructs the residue-field embedding with `Ideal.ResidueField.lift`.
It proves the prime lies over p and the factorization agrees on R, uses Mathlib's
open-immersion and étale-composition instances, and constructs the morphism in the
existing induced Under/Over category. The localized image of f is a unit.
The existing theorem signature, docstring, public import, and DAG route are unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement`
(node `lem-weil-pbc-etale-triple-unit-refinement`), the module's one sorry.
No holes added; no sorry remains in this delivery. Local single-file compilation
passes without warnings. A temporary `#print axioms` check reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. The original public import is retained. The final proof adds no imports and
uses the existing Mathlib leaf `lem-weil-pbc-etale-composition-cancellation` through
the open-immersion and composition instances already available. No nodes or modules
of the original route are bypassed. No new auxiliary modules or nodes are delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The DAG's kernel and residue-field
construction is implemented directly; the unit route is preserved. An initial
scratch draft merely restated invertibility with an inverse witness; it was
removed entirely and is not part of the delivery.

## Second reading by U2

1. Compared the delivered module with the repository version. The theorem signature,
   docstring, visibility, and public import are byte-for-byte unchanged; only the
   proof body changed. Verdict: pass.
2. Compiled the module and all sandbox modules successfully. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` remains. The axiom audit reports
   only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and searched the library for duplicate declarations. The
   kernel, localization, and residue-field constructions are needed for the stated
   argument; no split-off statement or duplicate declaration was introduced. Verdict:
   pass.
4. Checked pruning and imports. The existing public import is required by the
   theorem's statement, no proof-only import was added, and no prior proof dependency
   is bypassed. Verdict: pass.
5. Compared the Lean proof with the DAG node and unit route. The proof realizes the
   node's localization and residue-field steps and preserves the `sk-thm-p1` route;
   the node metadata remains consistent. Verdict: pass.

Changed only this report; no Lean statements, definitions, imports, or DAG nodes were
modified.
