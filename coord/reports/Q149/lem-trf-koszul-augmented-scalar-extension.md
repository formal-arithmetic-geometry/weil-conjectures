## Files written

- `dag/nodes/sec-trace-formula/lem-trf-koszul-augmented-scalar-extension.json`: item split into six proof steps; statement unchanged; not a Mathlib leaf.
- `citations.json`: twelve verbatim excerpts, one per cited node per proof step.
- `report.md`: this report. The prescribed search command also wrote `searches.jsonl`.

No new nodes; no new Mathlib leaves. The sandbox initially had no item, report, or search log, so the item was copied from the read-only live repository. No repository file was written, no git command was run there, and no Lean, compiler, Lake, or build tool was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, augmented Koszul complexes, and Koszul scalar/base change found no declaration covering this item's quotient isomorphism, prescribed wedge normalization, and augmentation square together. `ExteriorAlgebra.nonempty_koszulBaseChangeIso` in `RingTheory/KoszulBaseChangeIso.lean` covers existence of an unaugmented chain isomorphism only. I read its statement and proof. Its statement does not specify the map on wedges or say anything about augmentations, so it cannot attach this item or justify those clauses by citation.

## Wanted literature

None.

## Findings and corrections

The item is true as stated; no STATEMENT-DISPUTED correction is needed. The imported proof was empty. The new proof makes explicit the augmentation compatibility that the first equality of Stacks 062H does not state. Flatness in the hypotheses of that Stacks lemma is needed for its regularity conclusions, not for the complex identity: the displayed inverse coordinate maps and their differential equation prove the identity here for an arbitrary ring homomorphism.

The definition of mixed total tensor puts the output-ring action through its first argument. I checked that our convention with the action on the second tensor factor is obtained by swapping factors when the scalar complex is concentrated in degree zero; no Koszul sign appears. This is spelled out in step 2 rather than treating the output action as an unstated identification.

The existing nodes `lem-sc-koszul-base-change-iso`, `lem-weil-pbc-tensor-quotient-base-change`, `lem-weil-pbc-exterior-power-free-basis`, and the item's three notion nodes were read. The quotient and basis nodes already supply all non-elementary algebraic inputs. The coordinate map and its explicit inverse, the alternating differential calculation, and the augmentation calculation are direct uses of these statements and definitions, not new nodes restating clauses of the item. In particular no arbitrary isomorphism from the existence-only Koszul node is asserted to preserve augmentations.

## Searches and blueprint route

I read the chapter and unit records, GOAL.md, the three levels in SETUP.md, and the stage-1 rules. There is no repair note for this item. The unit/chapter route and inherited blueprint ancestry are unchanged. I read the current main-20261015 statement and proof of `lem-trf-local-term-locality`; the item is an auxiliary algebraic input in the existing long refinement chain, not that blueprint theorem's own statement.

Whole-DAG searches included Koszul scalar/base change, tensor quotients, exterior bases and `quotIdealMapEquivTensorQuot`, and the source tag 062H. `tools/blueprint_refs.py ancestor` identified `lem-trf-local-term-locality`. Whole-blueprint searches `Koszul` and `tensor quotient` found no imported blueprint statement giving the full augmented comparison. Thus the item's `same_as` remains empty. No new node needed a separate duplicate comparison.

I ran the prescribed `msearch.py` commands for the item with LeanFinder, Loogle, grep, and LeanSearch, then a second LeanFinder phrasing. I read each output and the five JSONL log records, and appended those actual searches to the item's existing historical records without discarding them. Loogle returned the quotient-tensor equivalence and its two formulas; the grep output located its file, whose definitions and formula lemmas I read at lines 36--85. The LeanFinder results concerned cotangent complexes and Kähler differentials; LeanSearch returned truncation/augmentation and unrelated change-of-scalars facts. These do not give the augmented Koszul comparison. The quotient input is already the existing Mathlib leaf, so no duplicate leaf was created.

## Review by Q149

I read delivery-errors B--E in full and checked the actual item and cited statements against their content requirements. My source for the item is `literature/stacks-project/more-algebra.tex`: definitions `definition-koszul` (Tag 0622) and `definition-koszul-complex` (Tag 0623), the displayed alternating differential immediately after the first definition, and the first identity in the proof of `lemma-koszul-regular-flat-base-change` (Tag 062H). I verified these tag/label pairs in `tags/tags`. I also read `algebra.tex`, `lemma-tensor-product-exact` (00DF), for the quotient tensor source, and the Mathlib quotient implementation. There are no new nodes whose separate sources need review. The proof is marked agent-written because the quotient normalization and commuting square are supplied explicitly, rather than being attributed to an unstated clause of Stacks.

For step 1 I opened `lem-weil-pbc-tensor-quotient-base-change`: its statement says both the quotient algebra isomorphism and both element formulas, including the finitely generated ideal specialization. Its hypotheses require only commutative rings and a homomorphism, exactly what is available. `def-weil-pbc-module-tensor-product` supplies balancing and generation; the explicit factor flip respects these relations. Thus the reversed tensor order and the requested inverse formula are justified, without invoking flatness or tensor exactness as an uncited theorem.

For step 2 I opened `def-pc-mixed-total-tensor`: it explicitly states the direct-sum terms, signed differential, and functoriality. Only one summand remains when the scalar complex is in degree zero. Its differential is zero, and moving that factor to the first position produces no graded sign. This proves both the scalar action convention and the identification of the tensor of the quotient single complex.

For step 3 I opened `lem-weil-pbc-exterior-power-free-basis`: it explicitly gives the ordered-subset wedge bases over any commutative ring, including the degree-zero and above-rank assertions. `def-weil-pbc-module-tensor-product` explicitly gives the universal property, balancing relations, and pure-tensor generation. Coordinates in these bases define the forward balanced map and the inverse. The two inverse equations are written out; no theorem about exterior powers commuting with arbitrary base change is assumed.

For step 4 I opened `def-weil-pbc-koszul-complex`: its statement contains the complete alternating differential formula, as well as the zero outgoing differential in chain degree zero. Applying the coordinate map changes exactly each coefficient g_i to its image under the ring homomorphism. The tensor definition supplies generation, so checking standard wedges tensored with scalars suffices. `def-weil-abstract-derived-category` explicitly defines cochain maps by commutation with differentials; the component inverse maps give the inverse cochain map. This yields a complex isomorphism, subsequently localized, rather than merely independent cohomology isomorphisms.

For step 5 the same Koszul statement gives d(e_i)=g_i, proving that the quotient augmentation kills the only relevant differential. The tensor statement supplies pure-tensor generation. Both composites are evaluated as the class of phi(a)s in degree zero and are zero elsewhere; the actual square is proved, not described as a transport or asserted from the existence of an unspecified isomorphism.

For step 6 the derived-category statement explicitly supplies the localization functor from complexes. A functor carries the already constructed pair of inverse maps to inverse maps and preserves the equality of composites; no derived tensor product computation or preservation of quasi-isomorphisms by an arbitrary scalar functor is being assumed.

I tested the statement and formulas at r=0 (I=0 and the tensor unit), r=1 (the two-term multiplication complex and its quotient), and q>r (zero terms). A useful nonflat example is A=Z, S=Z/2Z, g=(2): the base-changed differential is zero and matches K_S(0), while the degree-zero augmentation square still commutes. For g=(1), the quotient is zero and the square is the zero map. If S is the zero ring all target modules and tensors are zero; if A is zero a unital map forces S zero. The coordinate and inverse identities remain valid. None of the arguments assumes a proper ideal, a regular sequence, nonzero rings, or an injective coefficient map.

All six steps are shorter than 2000 characters. The elementary markings are supported by the written coordinate identities and definition specializations; step 1 explicitly cites the non-elementary quotient isomorphism and is not marked elementary. Every node used by a step is in `proof_deps`; every citation excerpt was copied verbatim from that node's statement. No new proof dependency points to a node above the item. No SGA source is used. No unit record needs realization edits because this created auxiliary item is not a unit key node.

## Repair of the returned delivery

The return dated 2026-10-23 04:13 UTC names delivery head `9164b0b55c8`. It says the reader approved the mathematics, but the landing refused a side-project completion that had not been promoted into the live DAG. I continued the retained delivered node, report, citations and search log rather than replacing them. The current repository item is `unsplit` with empty proof and proof dependencies; its statement, statement dependencies, source, chapter, unit and blueprint ancestry agree with the retained version. There is no released stage-1 repair note. The first required dry run completed successfully at `fab9b2971e7`, using the delivery tool's current `origin/sheaf-dag` base; it did not push.

I re-read all six current dependency statements, rather than assuming an old citation remained valid: `lem-weil-pbc-tensor-quotient-base-change`, `def-weil-pbc-module-tensor-product`, `def-pc-mixed-total-tensor`, `lem-weil-pbc-exterior-power-free-basis`, `def-weil-pbc-koszul-complex`, and `def-weil-abstract-derived-category`. None is merged away. Their present statements give exactly the quotient formulas, tensor relations and generation, mixed totalization, wedge bases, alternating differential, and localization used in the retained proof. All eleven retained citation quotes are still verbatim substrings of these current statements. I retained the actual recorded searches after reading their results; the statement and search question have not changed, so no repeat search is warranted.

The repaired split makes the mixed-tensor convention precise in step 2: take base ring A and output ring S, put S[0] in the first argument, and put E in the second. The differential sign is explicitly (-1)^0=1. The written factor flip then gives E tensor_A S, its S-action, its differential and functoriality. I added the module-tensor definition to that step's uses and a twelfth verbatim citation quote. Step 4 now also derives the inverse cochain-map equation by multiplying the forward differential identity by the explicit inverse components. These are actual proof clarifications beyond an unchanged re-push, and introduce no new lemma or hypothesis.

I rechecked B--E on the repaired files: the statement is self-contained and unchanged; every non-elementary input is an existing cited statement; the explicit maps prove the normalization and square; no new node restates a clause, no unsupported existence is used to choose a normalized map, and no flatness or regularity is introduced. All steps remain below 2000 characters. The empty sequence, one-element sequence, zero-ring and nonflat Z to Z/2 cases described above still satisfy the formulas. No source, target, unit or chapter route changes. The delivery tool performs the rebase onto its freshly fetched current DAG while preserving maintainer-owned fields; final validation and push follow with the repaired sandbox.

## Unfinished work

None in the mathematical repair. The repaired files must pass the final server dry run before direct delivery.
