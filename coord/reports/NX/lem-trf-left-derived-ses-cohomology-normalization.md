## Files written

- `dag/nodes/sec-trace-formula/lem-trf-left-derived-ses-cohomology-normalization.json`: statement, split in three steps; no whole-statement Mathlib match. The statement and its statement dependencies are unchanged.
- `citations.json`: one entry for each of the three node citations, quoting the actual current statements verbatim.
- `searches.jsonl`: the required search command's original records for this item. Five fresh searches (LeanFinder twice, Loogle, grep and LeanSearch) supplement the retained inherited searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The already existing Mathlib leaf `lem-sf-derived-homology-long-exact` is reused.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, left-derived short-exact cohomology terminology, `leftDerivedZero`, and `fromLeftDerivedZero`. No project declaration states every clause with a closed proof. General homology-sequence statements in `CategoryTheory/DerivedCategory/IsoOfSyzygies.lean` and the right-derived-functor folder do not identify the total-left-derived counit in degree zero for a merely right exact functor.

## WANTED

None. All mathematical sources used are available in `literature/stacks-project/derived.tex`.

## Findings and corrections

The imported node was statement-only. Its statement is correct: it already assumes the displayed triangle distinguished, so this item does not need to prove that total derivation preserves triangles or that the short exact sequence produces the given triangle. The parent has a separate triangle input. I retained all hypotheses, the actual counit, and the specified maps. There is no statement dispute.

The substantive single-object input is already `lem-trf-left-derived-object-cohomology`; it states the exact total-derived counit normalization, naturality and vanishing required here. Creating a replacement would duplicate it. The long exact sequence is already `lem-sf-derived-homology-long-exact`, a Mathlib leaf. After these two citations the remaining work is the elementary change of objects by the degree-zero isomorphisms. I wrote its three arrow formulas explicitly, including the incoming connecting map and the final epimorphism.

Read the current `dag/units/sk-i-curve-zero.json` and `dag/chapters/sec-trace-formula.json`, and the latest blueprint's `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. The inherited ancestor records the longer nearby-cycle/semistable-modification support chain. This generic homological item follows its own Stacks 015D support route, and changes neither the unit nor the chapter. It is not the unit's key statement; no unit realization field is changed.

## Not duplicates

No new node was created. Existing nodes reused: `lem-trf-left-derived-object-cohomology` for the actual degree-zero counit, and `lem-sf-derived-homology-long-exact` for arbitrary distinguished triangles. Searches of the whole imported blueprint for `left derived`, `cohomology sequence`, `counit normalization`, and `higher derived` did not find a blueprint node stating this generic normalization result. The cohomology-sequence hit `pqf-def-cohomology` concerns sheaf cohomology on a scheme; the counit-normalization hit `det-sp-composition-comparisons` concerns exceptional-operation composition maps, not this functor. Searches for Tags 015D, 05TC and 05TD identify the already existing single-object and short-exact-sequence family, all retained as existing nodes.

## Review by NX

I read Stacks `derived.tex`, Tag 015D (`lemma-F-acyclic-ses`) including its proof: its exact cohomology sequence uses negative-degree vanishing and the canonical identification of degree zero for right derivation. Reversing the convention gives precisely the left-derived degree-zero tail here. I also read Tag 05RS (`lemma-cohomology-homological` and the following long exact sequence), Tag 05TC (`lemma-negative-vanishing`), Tag 05TD (`lemma-left-exact-higher-derived`, including the canonical-map assertion), and Tag 05T5 (`lemma-irrelevant`, especially parts (3) and (4) relating unbounded and bounded-above derivation). The split cites existing nodes for these inputs rather than using source tags as substitutes for node statements. No prohibited SGA route is involved.

For step 1 I opened the statement of `lem-sf-derived-homology-long-exact`. It explicitly gives exactness at all three positions for an arbitrary distinguished triangle in the derived category of any abelian category, with the first and second arrows the cohomology images of the displayed maps. Here the target category is the given abelian category B and distinguishedness is a hypothesis. Thus the maps really are T^q(i), T^q(p) and the connecting map associated to the stipulated w. Its Mathlib declarations were read in `Algebra/Homology/DerivedCategory/HomologySequence.lean`: the connecting-map definition and exactness statements apply in this generality. No preservation-of-triangles fact is silently assumed.

For step 2 I opened the entire statement and proof of `lem-trf-left-derived-object-cohomology`. Its abelian categories, enough projectives, additive right exact V, and everywhere-defined total left derivation in the essentially-constant denominator sense are exactly the item's hypotheses. Crucially, it specifies c_N as H^0 of the canonical counit, gives its isomorphism, gives its naturality equation for every f, and gives all positive-degree vanishings. I use these clauses of its statement, not its projective-resolution proof or its additional acyclicity criterion. There is no cycle: its proof dependencies are projective replacement, denominator initiality, essential pro-evaluation and definition nodes, never this item.

For step 3 I read `def-sp-abelian`: the category has kernels and cokernels, hence image subobjects, and monomorphisms/epimorphisms have the stated kernel/cokernel properties. This step uses the already established steps 1 and 2. Conjugating the two degree-zero maps by the c isomorphisms gives V(i), V(p) by the explicitly stated naturality equation; the first arrow has only target conjugation, hence is c_{M'} composed with the connecting map. Kernel and image universal properties are unchanged by composing with inverse isomorphisms, so exactness transfers at every one of the three new objects. The vanishing used at the last spot is T^1(M')=0, which is unconditional here. This calculation is elementary and is not made into another node.

I checked small cases: for V the identity, T^q vanishes outside zero and the tail is the original short exact sequence; for V zero every object and arrow vanishes; for V=- tensor_Z Z/n and the sequence 0 -> Z --n--> Z -> Z/n -> 0, the objects need not be acyclic and the incoming connecting map can be nonzero, so no spurious initial zero was inserted. For a noncanonical distinguished triangle with the prescribed first two arrows the same triangle-cohomology theorem applies to its own w; the statement does not claim independence of w. All maps have the asserted sources and targets, including c_{M'} partial^{-1}. There are no new statements requiring further edge-case tests.

I compared against delivery-errors B--E: no statement-only child carries a hidden proof (there are no children); every non-elementary input is in a cited statement; the canonical comparison is not replaced by an arbitrary isomorphism; the proof is not a relabeling into clause nodes; the elementary invariance of exactness is actually explained. The three proof steps have fewer than 2000 characters each and the full assembly has fewer than 3000 characters. `citations.json` quotes each cited node's statement verbatim. Existing searches and metadata were preserved. No Lean, repository or launcher file was written, and no compiler/build tool was run.

## Unfinished work

None in the mathematical split. The required server dry run passed; see the validation record below.

## Validation

The required `deliver.py NX lem-trf-left-derived-ses-cohomology-normalization --no-push` exited 0 and printed `OK (not pushed)` at commit `213ed8d35df`, with server preflight passed. The final report is included in the subsequent final validation and push. No local DAG checker or Lean compiler was invoked.
