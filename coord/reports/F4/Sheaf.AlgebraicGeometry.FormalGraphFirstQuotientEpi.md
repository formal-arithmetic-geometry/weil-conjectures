## What changed

Proved `AlgebraicGeometry.formalGraph_first_quotient_epi` with its existing signature
byte for byte unchanged. The proof completes the coherent pullback, lifts into the
completed discrepancy kernel and evaluates the resulting split epimorphism at index zero.
The new proof-only import `Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero` supplies
`AlgebraicGeometry.formalGraph_discrepancy_zero`, now proved in the second reading.
No existing public signature, definition or public import changes.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.formalGraph_first_quotient_epi`, node
`lem-weil-pbc-formal-graph-first-quotient-epi` (1 of 1 original holes).
Added holes: none. Remaining holes in the delivery: none. The initially split-off
`AlgebraicGeometry.formalGraph_discrepancy_zero`, node
`lem-weil-pbc-formal-graph-discrepancy-zero`, is also proved in this delivery.
Thus this is a proof, not a decomposition; net original holes closed minus added holes is 1.

Both delivered files compile cleanly through `lcompile.py --all`. A scratch axiom probe
prints exactly `[propext, Classical.choice, Quot.sound]` for both public theorems.
There are no forbidden declarations, hollow definitions or data chosen from unproved
existence statements. The pullback/kernel lifts are used only within theorem proofs.

## No longer needed

Removed `import all Sheaf.AlgebraicGeometry.CoherentFormalModule` from the item: no
private declaration from that compatibility module is used. The new discrepancy proof
instead needs `import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule` for
the upstream quotient-annihilation and ideal-product-monomorphism helpers.
Removed the item's direct proof import of
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelFactorization` and moved its private
`formal_zero_of_level` helper into the discrepancy module, where it is actually used.
The discrepancy module imports and uses `formalTransition_epi` from that dependency.
Accordingly the parent node replaces its direct
`lem-weil-pbc-formal-kernel-factorization` dependency by
`lem-weil-pbc-formal-graph-discrepancy-zero`; the former stays a dependency of the latter.
No dependency module becomes unreachable, and no whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker left the completed-discrepancy calculation as a new hole despite the
available quotient-annihilation and stabilization lemmas. The second reading closes it.
The first worker also omitted the parent node update for the newly invoked discrepancy
lemma; this delivery corrects its proof, proof_deps and proof_origin.
The initial report described the target as proved while leaving its newly introduced
component lemma open; the counts above distinguish those situations.

## New nodes

`lem-weil-pbc-formal-graph-discrepancy-zero`, in
`lean/Sheaf/AlgebraicGeometry/FormalGraphDiscrepancyZero.lean`, isolates and proves just
the completed discrepancy calculation. It assumes an arbitrary coherent P and two
completed projection identities; it does not assert the graph projection is epi.
Its statement is a strictly smaller intermediate step, not a restatement of the item.
The node has a self-contained statement, exact Lean signature, source, proof steps,
creation/blueprint records and search records. No change record is needed: no existing
public statement, definition or visibility changed.

## Second reading by F4

1. Compared each delivered file to the shared repository. The new discrepancy module
   is absent there. The existing target theorem's signature is byte-for-byte identical;
   its public import and definitions are unchanged. The only removed declaration is an
   unused private proof helper, moved verbatim into the new module. Verdict: pass.
2. Compiled both modules in dependency order with no warnings or errors. Searched all
   delivered Lean text for sorry and forbidden constructs; none remain. A scratch
   `#print axioms` probe for both public theorems reports only propext, Classical.choice
   and Quot.sound, with no sorryAx. Verdict: pass.
3. Read the new discrepancy statement against every binder and conclusion. For J=0
   it is the ordinary zero difference q-p theta; for J=1 all quotient terms vanish;
   n=0, zero modules and the empty scheme require no extra assumption. Quotients of Q
   inherit J^(n+1)-annihilation, its completed transitions above n are invertible, and
   formal source transitions below n are epi. Those facts prove the new statement
   without needing a pullback or any epi conclusion. Repeated LeanFinder, Loogle and
   Mathlib grep searches with new queries, then rg in both library roots: no duplicate
   discrepancy theorem; existing stabilization/quotient/transition lemmas are used.
   Related formal-map detection proves a different separating-kernel assertion.
   No split-off sorry is left. Verdict: pass after closing the component lemma.
4. Reviewed the full categorical argument top down: exact completion preserves the
   coherent pullback and kernel, g has the stated projection components, the discrepancy
   vanishes, and the level-zero section splits the reduced first projection. The final
   cokernel-projection factorization gives exactly the original epi. Checked imports
   and removed the unused private-import access and moved helper/direct dependency.
   Read `dag/units/sk-thm-p1.json`, including `realized`: this is below its unit steps;
   no realized statement, step, chapter route or unit route is bypassed. Verdict: pass.
5. Checked both nodes against the actual Lean. Updated the parent's second proof step
   and dependency union to cite the new discrepancy node. Expanded the new node proof
   to the actual quotient-annihilation, reduced discrepancy and naturality calculations,
   retaining its transition-factorization dependency. Its lean.statement equals the
   public declaration signature; all new-node metadata and searches are present.
   Verdict: pass after the parent-node repair.

Second-reading changes: proved `formalGraph_discrepancy_zero`; moved the existing
private zero-propagation helper to its user; pruned the corresponding unused imports;
added the new module docstring; repaired node metadata and the hole counts in this report.
