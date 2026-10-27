# Stage-1 delivery: lem-sfb-space-qc-open-boundary-ideal

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-open-boundary-ideal.json` (statement, split, no Mathlib match); `citations.json` (one verbatim statement excerpt for each proof-step citation); this report. No new nodes or Mathlib leaves. `searches.jsonl` contains the actual five searches, and `prepare.py` records the sandbox preparation.
2. Attachments: none. Searched all `lean/WeilConjectures/` for the item tag and boundary-ideal names, and searched the algebraic-geometry sources by concept. The boundary tensor constructions concern schemes and different conclusions. No exact project proof was found.
3. WANTED: none.
4. The imported item is mathematically correct. Its proof was empty. The statement and existing provenance are preserved. The split now exposes the finite-type selection argument instead of invoking Tag 0855 as a black box or creating a new node that restates it.
5. Unfinished work: none for this one-level stage-1 split. The existing approximation and ideal-correspondence nodes retain their independent downstream work.

## Searches and reuse

Read Stacks `spaces-limits.tex`, Tag 0855 (`lemma-quasi-coherent-finite-type-ideals`), especially the entire (2) to (3) argument; Tag 0829 (`lemma-directed-colimit-finite-type`) and its image-of-finitely-presented-modules proof; and `spaces-properties.tex`, Tag 03IQ (`lemma-reduced-closed-subspace`). Read the chapter and unit records and the current `literature/blueprint/latest/` unit statement, main proof and direct-image proof. This is an inherited supporting input for the compactification/proper-support construction, below the unit route, rather than a replacement of a unit step. The imported ancestor is null in this chain; that provenance was retained, including the inherited exact place.

Searched the entire DAG by Tag 0855, by the approximation and reduced-support tags/labels, and by statement concepts. Read the candidate statements in full, including the Noetherian coherent-union node, the general finitely-presented approximation, affine-chart calculus, reduced support and the ideal correspondence. The Noetherian coherent-union lemma cannot be used here. The finitely-presented approximation works without that hypothesis and already implies the required finite-type selection by the explicit steps below. Blueprint searches for `finite type ideals`, `boundary`, `finite presentation`, and `boundary ideal` found no blueprint statement identifying this algebraic-space lemma; the scheme boundary results do not state it.

Ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle and Mathlib grep through the mandated logging command. Read the hits. In particular `PrimeSpectrum.isCompact_isOpen_iff_ideal` (`Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1008`) is only the affine prime-spectrum statement; `IdealSheafData` support results in `Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean` do not construct a finite-type ideal on an arbitrary algebraic space. The item is not a Mathlib leaf. Its inherited searches remain intact and the five fresh queries are appended exactly as run, with their actual logged results.

## Not duplicates

No new nodes were created. Reused the existing reduced-support, ideal-correspondence, finitely-presented approximation, affine-atlas, affine-chart calculus and filtered-module-colimit nodes. In particular I did not create a Tag 0829 node: its short image argument is already realized here from the existing approximation and chart-calculus statements.

## Review by Q44

I checked B–E against the source and all cited statements. There are six steps, each shorter than 2000 characters; no long step hides a comparison lemma or an unrecorded standard theorem.

Step 1 uses `lem-sfb-space-reduced-closed-support` for existence with exactly the closed support C, and its base-change support clause. `lem-sfb-space-ideal-closed-subspace-correspondence` supplies the quasi-coherent kernel ideal and the restriction/quotient assertions. The empty base change over U has zero quotient, so J restricts to the unit ideal. Reducedness is used only to choose Z, never imposed on T.

Step 2 uses `lem-sfb-space-module-fp-directed-approximation` for a SMALL FILTERED diagram and its colimit in ALL module sheaves, exactly what its statement promises. The space T is qcqs in the absolute-diagonal sense required there. The atlas definition of quasi-compactness gives topological quasi-compactness by its continuous surjective point map, the same argument written in step 3. No finite presentation of J is assumed, and the maps from the approximations are not assumed injective.

Step 3 uses `lem-a1-space-point-open-calculus` for continuity and scheme-test surjectivity versus point surjectivity. This checks the topological compactness hypothesis of `lem-sfb-qc-space-affine-etale-atlas` for U. That statement gives a SINGLE AFFINE surjective etale atlas; no affine intersections are presumed. I read `lem-weil-pbc-etale-composition-cancellation`: its first two clauses give exactly the two scheme assertions needed on each scheme base change to prove that the composite W to T is etale. The representable definition is unfolded on those tests, not silently generalized from schemes.

Step 4 uses `lem-sfb-space-qcoh-affine-chart-calculus` for evaluation of filtered colimits on W, which is now an affine etale object of T. The ring on this chart is A and J(W)=A because W lies over U. The first clause of `lem-weil-pbc-filtered-colimit-modules-elementwise` then lifts 1 from a SINGLE stage, in the category of A-modules with the required small filtered index. This avoids an unjustified claim that arbitrary sheaf colimits are evaluated sectionwise.

Step 5 uses the image and finite-presentation testing clauses of the SAME affine-chart-calculus statement. A finite presentation gives finitely many generators, whose images generate the image module; hence K is finite type. This finite-generating-set argument and the sheaf-local zero quotient are elementary deductions from the cited statement, not additional theorem nodes. K is a submodule of the structure sheaf, so it is an ideal. The atlas is surjective, so equality with the unit ideal there proves equality on U.

Step 6 uses the inclusion-reversing correspondence for the direction C contained in V(K). It uses the point/open-subspace calculus to test the reverse inclusion on a field representative: a point lying in U factors through U on that scheme test, contradicting the empty unit-ideal zero locus. Thus the conclusion is equality of supports, with no unsupported equality of ideals or reduced structures.

The generic point-topology lemma is declared in `split_report.tool_uses` because it is filed in another unit; the scheme etale-composition lemma and module element-representation lemma are already Mathlib leaves. All other proof inputs belong to this unit. I opened every cited node and verified the quotations in `citations.json` are verbatim substrings of the statements, not their proofs. There is no citation of an item's clause disguised as a new lemma and no new dependency on this item from any cited node.

Edge cases checked: U empty (one may take K=0, and the proof also works using the empty affine atlas and filtered nonemptiness), U=T (the chosen image is the unit ideal after the covering test), T empty (Spec of the zero ring is allowed as atlas), nonreduced affine T (the initial radical ideal need not be finite type), and non-Noetherian T (finite type is obtained from finite presentations and their images, not coherence or Noetherianity). None requires a statement correction.
