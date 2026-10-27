# Worker report: lem-sfb-rational-linear-hom

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-linear-hom.json`: statement, now split; no Mathlib match for the complete rational affine-group-scheme assertion.
- `citations.json`: one verbatim statement quotation for every citation in every proof step.
- `searches.jsonl`: actual search-command output records, retained unchanged.
- `report.md`: this report. `milne.txt` is a local text extraction of the source PDF for reading, not a delivered DAG file.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses the existing general affine coaction-linearization theorem; it does not rename the item's clauses as new lemmas.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the blueprint id, rational representation/module terminology, comodules, linear Hom and conjugation. No project declaration states the item's rational coaction assertion. Abstract-group Hom representations do not establish this item.

## WANTED

None. Read the available `literature/milne-algebraic-groups_iAG2017.pdf`, Chapter 4(a), Remark 4.1, printed pp.83–84, and Lemma 22.40 (b) to (a), printed p.477; also read the identity and cocycle diagrams of Stacks Tag 03LF (`groupoids.tex`, `definition-equivariant-module`). The original source explicitly asserts the natural Hom action and uses fixed maps as equivariant maps; the detailed linearization proof is marked agent-written because it expands that assertion using an existing DAG theorem.

## Problems found and changes

The item's mathematical statement is correct and all its original hypotheses and conclusions are retained. Added references for tensor products, scalar extensions, and the affine spectrum, and made the implicit equality $G=\operatorname{Spec}k[G]$ explicit. No finite-type hypothesis was added.

The tempting existing `lem-sfb-rational-representation-comodule-dictionary` assumes that the group scheme is of finite type. It cannot be used here. Instead `lem-sfb-hopf-coaction-linearization` explicitly has no finite-type assumption and supplies the needed coaction/linearization equivalence, inverse, and cocycle. It belongs to the item's unit `sk-thm-sf-ctf-stability`, so no off-unit tool use is introduced. The inherited blueprint ancestry already has `from.node=null`; the full supporting place and via chain are preserved. This item is a supporting node, not the unit key statement, so no unit record is changed.

Retained the inherited Mathlib search history and appended five actually run searches: LeanFinder in two phrasings, Loogle, LeanSearch and grep. Read `Representation.linHom` and `linHom_apply`, `RepresentationTheory/Basic.lean:663–675`, and `linHom.mem_invariants_iff_comm` / `invariantsEquivRepHom`, `RepresentationTheory/Invariants.lean:190–212`. These concern one abstract group. The other returned candidates concern Hopf antipode identities or the ordinary internal Hom/rigidity of finite-dimensional modules; none supplies the rational affine-group-scheme coaction. All services responded successfully. No unrun search is recorded.

## Unfinished work

None in this split. Downstream existing unsplit dependencies retain their own stage-1 work; no claim about a completed Lean proof is made.

## Not duplicates

No new nodes. Searched the full DAG for coactions, comodules and Hom base change, and the full blueprint with `tools/blueprint_refs.py search` for coaction, linear Hom, conjugation and linearization. This found the reusable affine linearization node in the DAG; the other representation/comodule dictionary is narrower. The blueprint conjugation results concern Weil sheaves, monodromy and abstract-group actions, not rational representations of arbitrary affine group schemes. No same-statement blueprint node was found.

## Review by Q44

I checked B–E against the actual item, the source text, and the cited statements, not just their titles. There are no new statement-only files, new identifiers or Mathlib leaves needing B1/B2/B5/B6/B8 checks. The item's notions have definition references; its TeX is stored with ordinary JSON escaping. Existing source citations are unchanged, the blueprint place is retained, and the same_as search found no equivalent blueprint statement. The source's Lemma 22.40 itself assumes the character group is zero, but that assumption is used later for fixed lines, not for its natural Hom action. Remark 4.1 and the unrestricted affine linearization node justify using the action construction without that assumption here.

Step 1 uses exactly `def-weil-pbc-module-tensor-product` (generation by pure tensors and the bilinear universal property) and `def-weil-module-base-change` (the induced maps on pure tensors). It writes out the matrix inverse to the Hom base-change map, including the expansion identities for the extended bases. Thus it does not invoke an unrecorded Hom/base-change theorem. The finite bases exist by the finite-dimensional hypotheses, and the displayed inverse is finite. Commutation with coefficient maps is immediate on each coefficient and pure tensor.

Step 2 uses the actual statement of `lem-sfb-hopf-coaction-linearization`, which supplies the bijection, the inverse map and the identity/cocycle. For E=k the coaction is a↦a⊗1 and the two algebra structure maps coincide; the two module coactions in the item satisfy every input equation. There is no smoothness, reducedness, finite-type, or nonzero-module hypothesis in this cited node. The cocycle order D_12=D_1 D_2 agrees with its composition convention.

Step 3 is a direct calculation from steps 1 and 2: conjugation has inverse T↦D_W^{-1}TD_V, and its two-factor cocycle is the displayed equality over C⊗C. The reversal of inverse order is written explicitly, so the argument does not silently commute the group actions. This is a few-line elementary computation, not a concealed lemma about rational representations.

Step 4 uses the reverse direction of the same existing node, whose statement actually produces a coaction satisfying the counit and coassociativity from the constructed linearization. This is a non-elementary application, marked accordingly. Pulling the already proved identity and cocycle back to (g,g^{-1}) proves that the pulled-back inverse is the action of g^{-1}; consequently the displayed action agrees with every clause of the item's formula after every algebra extension, not just over the ground field.

Step 5 quotes the existing node's morphism clause, which expressly equates commutation with linearizations and commutation with coactions. Cancelling the invertible D_V is elementary, and restriction to v⊗1 also checks that assertion directly. I read `def-weil-affine-spectrum`: it gives the contravariant ring-map/scheme-map correspondence, so the identity of C really supplies the universal C-valued point. The converse from all algebra-valued points is proved by that single universal point. It therefore does not use density of k-points or a reducedness assumption. All quotation substrings were checked against the live node statements before writing citations.json.

For the small cases, when V=0 or W=0, H=0 and the empty matrix expansions, unique automorphism of the zero module and fixed/equivariant equalities all still hold. For the trivial group the linearizations and conjugation are identities. For G_m and one-dimensional weights a,b the formula has weight b−a, as conjugation should. In positive characteristic the construction works over the coordinate algebra itself; in particular a nonreduced group such as μ_p is not replaced by its field-valued points. The unrestricted affine-group hypothesis is checked at both non-elementary applications. No statement dispute or source error was found. Every step is shorter than 2000 characters; all algebra and compatibility assertions are explicit. I corrected the initially tempting finite-type dictionary route by using the genuinely unrestricted existing node before finalizing the proof.
