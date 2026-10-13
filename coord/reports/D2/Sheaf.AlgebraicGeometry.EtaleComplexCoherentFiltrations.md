## What changed

Completed `AlgebraicGeometry.Etale.exists_etale_complex_coherent_filtrations`, preserving
its signature and public imports. Added proved private helpers for coordinate-swap
restriction, its homology isomorphism and naturality, and the induced spectral-sequence
functor. The main proof uses the existing uniform-bound, page-map-coherence,
colimit-below, image-filtration and filtration-vanishing theorems. It constructs the
page diagram, proves the filtration bounds, and uses one explicit common page bound
for all stages and the target at each q. Updated the existing node's proof,
proof_deps and proof_origin to match this assembly. No interface changes or adaptations.

## Proved and sorry left

Closed the module's one hole:
`AlgebraicGeometry.Etale.exists_etale_complex_coherent_filtrations`
(node `lem-weil-pbc-etale-complex-coherent-filtrations`).
No holes added or split off; no sorry remains in the delivered module.
The private helpers are all proved. Compilation through lcompile.py is clean.
The theorem uses existing dependencies; this does not claim that their complete
transitive import closure is sorry-free.

## No longer needed

Removed direct proof imports:
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.KInjectiveBridge`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleHypercohomologyFiltration`

The corresponding original direct proof dependencies `thm-sp-if-e1`,
`def-sp-kinjective-bridge`, `thm-sp-spectral-object-yields`, and
`lem-weil-pbc-hypercohomology-e1-pullback-functorial` are replaced at this node by
the existing uniform-bound and page-map-coherence interfaces. The filtration-zero
node remains used, through exports of the public statement dependencies.
These removals concern direct imports and DAG edges; the modules may remain in
transitive imports and no whole-library reachability pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox draft shadowed its stabilization-bound function R with the
page functor R; the bound function is now named bound. Its abutment-map calculation
also needed explicit unfolding of cohomology and the two global-sections composition
isomorphisms before functoriality and associativity apply. Broad transparency
relaxation caused repeated 60-second timeouts; it is now limited to the homology
naturality helper and the abutment-map calculation. The complete module compiles
within the fixed limit without changing definitions or splitting files.

The original DAG described the mathematical construction but did not name the
existing quantitative uniform-bound, diagram-coherence and colimit-below interfaces
used by the proof. Its proof fields now name those nodes. The unit's realized
statement/step lists are empty, so no fixed unit realization was bypassed.

## Second reading by D2

1. Compared the complete module with the repository using diff and separately compared
   the text from the existing theorem name through its proof delimiter: the signature
   is byte-for-byte identical. The existing docstring and public imports are unchanged.
   All added declarations are private proof helpers; no public definition or statement
   changes, change records, or forced adaptations are present. Verdict: pass.
2. Read the coordinate embedding, restriction homology naturality, sequence functor,
   and main assembly. The module compiles cleanly through lcompile.py (51.4 seconds).
   There is no sorry or forbidden declaration form in this module, and every helper
   has an explicit construction or proof. The presentation existence theorem is used
   by existential elimination inside a theorem, not to define a public arbitrary
   chosen object. Verdict: pass, subject to the axiom check recorded below.
3. No statements were split off and no holes were added. Checked the swap at r=1
   and the homology indices; the support bounds also cover p<a, p=a, and zero
   complexes. The bottom bound follows from p<max a (p+1), independent of whether
   the lower support bound is attained. Verdict: pass; no new-node search required.
4. Read the supplied uniform-bound, page-map-coherence and image-filtration interfaces.
   Searched Mathlib's restriction-homology API and the upstream and Sheaf sources for
   coordinate reindexing and coherent-filtration alternatives; found no ready-made
   replacement for the assembly or its swap naturality helper. The proof uses the
   existing restrictionHomologyIso, rather than reconstructing homology. Each plain
   import supplies a declaration used in the proof; the two public imports supply
   the statement's types and maps. The report lists all five removed imports and
   all four removed old proof dependencies. The unit sk-prop-h2 has realized
   statement=[] and steps=[[]], so no realized unit step is bypassed. No claim of
   whole-library reachability pruning is made. Verdict: pass.
5. Compared the node JSON with the repository. Only proof, proof_deps, and
   proof_origin changed. The six dependencies are exactly the union of the proof
   steps' uses, including the still-used filtration-zero theorem. The four steps
   describe the colimit bound, coordinate restriction, filtration bounds, and
   common-page stabilization actually written in Lean. No new nodes. Verdict: pass.

Second reading changed only this report; no mathematical or Lean repair was needed.

A scratch copy compiled with
`#print axioms AlgebraicGeometry.Etale.exists_etale_complex_coherent_filtrations`:
only propext, Classical.choice, Quot.sound, and sorryAx were reported (57.9 seconds).
The last comes from still-open imported dependencies; the delivered module contains
no holes. This completes point 2's axiom check without claiming a closed import closure.
