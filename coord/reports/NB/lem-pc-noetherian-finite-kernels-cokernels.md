# Stage-1 report: lem-pc-noetherian-finite-kernels-cokernels

## Files written

- dag/nodes/sec-picard-framework/lem-pc-noetherian-finite-kernels-cokernels.json: statement, Mathlib leaf; two declarations, one per clause. No new nodes.
- citations.json: empty list, since a Mathlib leaf has no proof steps or proof citations.
- searches.jsonl: actual msearch log. Every query recorded in the node was run; inherited searches were replaced by this run's results.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source for the item id and kernel/cokernel module-finiteness terminology found sheaf finiteness results and uses of Module.Finite.of_injective/of_surjective, not a project declaration stating both clauses for arbitrary finite modules. These do not qualify as attachments.

## Wanted sources

None.

## Corrections and findings

The item's statement is true and needs no correction. Its source was wrong: Tag 00F4 maps to algebra-lemma-compose-finite-type, not a lemma about Noetherian modules. Replaced it by 00FP (lemma-Noetherian-finite-type-is-finite-presentation), part (2), and 0519 (lemma-extension), part (3). The tag mapping and both statements and their proofs were read in literature/stacks-project/tags/tags and algebra.tex (6088 onward and 391 onward respectively). No STATEMENT-DISPUTED finding arises: the mathematical assertion is unchanged.

The earlier search verdict already suggested a general Mathlib result, but missed the direct one-clause specializations. The more general Module.Finite.of_injective and Module.Finite.quotient supply the clauses without a categorical equivalence or an additional theorem identifying definitions. LeanFinder returned the finite-module Noetherian instance on the second phrasing. LeanSearch returned Internal Server Error and is recorded unavailable. Single-file msearch grep has a display parsing issue (line numbers are printed as file fields); repeated the decisive greps on directories to obtain proper file and line data. This did not prevent the work.

## Unfinished work

None in stage 1. No Lean was written or compiled. The sandbox is for a fresh second reader; no push is requested.

## Not duplicates

No new nodes were created. Whole-DAG keyword/tag searches and blueprint_refs searches for finite kernels, kernels and cokernels, submodule of a finite, and Noetherian were inspected. No imported blueprint node found states exactly this arbitrary-module conjunction. Existing sheaf and coherent-module statements have different objects. The item itself remains the unique delivered node.

## Review by NB

I read the chapter sec-picard-framework and unit sk-thm-picard-semicon, together with the ancestor blueprint file lem-pc-noetherian-flat-complex-perfect.md. The ancestor's second proof paragraph explicitly invokes closure of finite modules under kernels and cokernels, and repeats that assertion in its downward finite-free construction. Recording this item as a Mathlib leaf realizes that same argument; it does not replace the unit or chapter route.

For the mathematical source, 00FP(2) assumes a Noetherian ring and says any submodule of a finite module is finite. Apply it to the actual submodule ker(f) of M; finiteness of N is unnecessary for this clause. The proof of 0519(3) says finiteness passes to the quotient in a short exact sequence, immediately from generators. Apply it to the quotient N/im(f): the images of any finite generating set of N generate this quotient. No finiteness of the image is assumed. Thus both source clauses agree with the item under all its stated hypotheses.

I opened both definition nodes in stmt_deps. def-weil-pbc-noetherian-ring defines a commutative ring with all ideals finitely generated and records IsNoetherianRing; def-weil-finitely-generated-module defines module finiteness by a finite generating set and records Module.Finite. The extra finite-ring discussion in that definition does not impose finite underlying cardinality on this item.

I read Mathlib/RingTheory/Noetherian/Basic.lean:136-139 in its Module namespace: Module.Finite.of_injective takes an injective semilinear map into a Noetherian module and returns Module.Finite for its domain. Specialize to the A-linear inclusion ker(f) into M, whose injectivity is simply subtype injectivity. I also read the global instance isNoetherian_of_isNoetherianRing_of_finite at 324-328: it assumes Ring A, AddCommGroup M, Module A M, IsNoetherianRing A, and Module.Finite A M, exactly the ring/module hypotheses in force. This instance supplies the required target-module Noetherian hypothesis; no manual theorem beyond the permitted inferred instance is hidden in the leaf.

For the other clause I read Mathlib/RingTheory/Finiteness/Basic.lean:264-267 in the Module.Finite namespace: quotient gives Module.Finite R (M / S) for any submodule S of a finite module M, with a scalar tower. Both scalar rings specialize to A, the ambient module to N, and S to LinearMap.range f. The scalar tower is the canonical self tower. The cokernel of an A-linear map is precisely this ordinary module quotient; this is not a sheaf or derived cokernel. The declarations and the inferred instance, with their files and lines, are all named in mathlib_match.how.

There are no numbered proof steps because the item is a leaf and no cited proof-node claims to audit under C4. The only statement citations are the two definition nodes just described. citations.json therefore correctly contains no entries. No clause was moved into a new child, and there are no new statement-only nodes, duplicate checks to justify, or new dependency edges that could create a cycle. The empty proof and proof_deps were retained.

I checked the zero ring and zero source/target cases, the zero map (kernel M and cokernel N), the identity map (both zero), and multiplication by 2 on Z (kernel zero and cokernel Z/2Z). The result imposes no injectivity or surjectivity requirement on f. To check the essential hypothesis, over a non-Noetherian ring with a non-finitely-generated ideal I the quotient map A to A/I has finite source and target but kernel I need not be finite; the Noetherian hypothesis was retained. The quotient clause remains valid even over such rings. I corrected only the erroneous source place and the missed Mathlib-leaf classification; no mathematical hypothesis or conclusion was altered.

The first dry run required proof_origin even for this Mathlib leaf. I filled its document provenance with the two checked Stacks places; the proof remains empty, as required for a leaf.

## Second reading by NB

- Item statement: checked against Stacks 00FP(2) and 0519(3), including Noetherian, finite-module, kernel, and cokernel hypotheses; verdict: agrees.
- Item source correction: verified 00F4 is unrelated and 00FP/0519 are the relevant algebra lemmas; verdict: repaired and documented.
- Proof steps: no explicit steps (Mathlib leaf); verdict: no uncited proof argument remains.
- Definition dependencies: checked `def-weil-pbc-noetherian-ring` and `def-weil-finitely-generated-module`; verdict: both define the notions used.
- Mathlib match: checked `Module.Finite.of_injective` (Basic.lean:136-139), the inferred Noetherian instance (Basic.lean:324-328), and `Module.Finite.quotient` (Finiteness/Basic.lean:264-267); verdict: each clause specializes exactly.
- New nodes: none; B1–B7 and duplicate checks are vacuous.
- Edge cases: checked zero modules/maps, identity, multiplication by 2 on $\mathbb Z$, and a non-Noetherian ideal counterexample; verdict: hypotheses and conclusions behave correctly.

Changes made: corrected the Stacks source tags and recorded the Mathlib leaf provenance/searches; no statement or node was otherwise changed.
