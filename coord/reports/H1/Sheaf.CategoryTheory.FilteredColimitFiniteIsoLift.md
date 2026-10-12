## What changed

Proved `CategoryTheory.filteredColimit_finite_iso_lift` directly in the original
module. Three private, proved helpers synchronize finite set-colimit equalities,
choose finite representatives above a fixed stage, and compare transported arrow
composites. The proof uses Mathlib's joint surjectivity, eventual equality and
`IsFiltered.wideSpan`, then aligns endpoints, enforces both inverse equations and
constructs the isomorphisms. Updated the existing node's proof and proof_origin.
Existing signatures and public imports are unchanged. The three added imports
(`Mathlib.CategoryTheory.Limits.Types.Filtered`, `Mathlib.Data.Finite.Prod`,
`Mathlib.Tactic.FinCases`) are plain proof imports.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.filteredColimit_finite_iso_lift`
(node `lem-weil-pbc-filtered-colimit-finite-iso-lift`).
Holes added: none. Sorries left in the delivery: none. This is a proof, not a
decomposition: one of one original holes closed, zero split off.
The private helpers `finite_stage_eq`, `finite_representatives_above` and
`arrow_comp_congr` are fully proved. A scratch-copy `#print axioms` of the main
theorem reports exactly `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed

No original proof dependency or import was removed. The old proof_deps contains
only `lem-weil-pbc-filtered-colimit-sets-elementwise`, whose Mathlib declarations
are used directly. No previously landed module is pruned.
Removed the first worker's unlanded common-inverse-representatives module and its
new node, and the redundant private Iso.mk wrapper. None is delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's split theorem merely expanded an isomorphism into its two
arrows and inverse equations, so it was equivalent to the item and not a genuine
reduction. Replaced that split with the full representative synchronization proof.
The original DAG route is valid and retained. The exact local literature files
are absent on this machine; checked the source online at
https://stacks.math.columbia.edu/tag/09YL (finite-diagram remark) and
https://stacks.math.columbia.edu/tag/04AX (eventual equality of set representatives).

## Second reading by H1

1. Compared the delivered module with the read-only repository version. The
   existing theorem signature is byte-for-byte unchanged, including all colimit
   hypotheses and the Arrow equality conclusion. No public definition or target
   statement changes. Verdict: pass.
2. The final module compiles locally without errors or warnings through lcompile.py.
   No sorry, axiom, unsafe, opaque, extern, implemented_by or hollow definition
   occurs. The main theorem's axiom list contains only the three permitted axioms.
   All representatives are chosen from proved Mathlib existence results, not an
   unproved existence theorem. Verdict: pass.
3. Rejected and removed the equivalent split statement. No split statement remains.
   Repeated searches with LeanFinder (finite common-stage elements / eventual
   equality), Loogle (IsColimit and Arrow), and rg over Mathlib and both local Lean
   roots. Mathlib provides the elementwise criteria and wideSpan; no direct theorem
   with the fixed-stage finite isomorphism conclusion was found. The existing
   category-iso and finite-functor theorems have canonical-colimit interfaces and
   do not give this fixed-stage conclusion directly. The new private helpers are
   elementary applications of the criteria. Empty families are valid because each
   wideSpan is based at an already supplied stage; a singleton is the ordinary
   arrow-and-inverse argument. No assumption of finite stage categories is used.
   Verdict: pass after repair.
4. The proof follows the three original node steps from the top downward, using
   Mathlib directly and no open Sheaf lemma. Proof imports are needed for the
   set-colimit criteria, finite products, and Fin 3 case analysis. All old proof
   dependencies remain used; no pruning is claimed. Read sk-thm-p1's realized
   record: this auxiliary node is below its fixed unit steps, and no unit route
   or realization was changed. Verdict: pass.
5. The existing node now records the actual arrow representatives, three endpoint
   equalities per index, two inverse equations per index, and final endpoint
   transport. Its proof_deps remains the elementwise set-colimit node, matching the
   Lean proof. No new node remains. Verdict: pass.

Second reading changed: removed the restatement split, proved the entire original
statement from Mathlib, added three private proved helpers and three plain proof
imports, and synchronized the node and this report with the final proof.
