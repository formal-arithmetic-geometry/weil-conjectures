# Stage-1 delivery: lem-trf-generic-free-cokernel-dimension-drop

## Files written

- dag/nodes/sec-trace-formula/lem-trf-generic-free-cokernel-dimension-drop.json: statement, split; no Mathlib match for the whole statement. Its statement and statement dependencies are unchanged.
- citations.json: one verbatim statement quotation for every node used by every proof step.
- report.md: worker report and self-review.

New nodes: 0. New Mathlib leaves: 0. The sandbox also retains searches.jsonl and the local JSON-writing helper. There was no prior item or report in the sandbox to resume.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for generic freeness, generic basis, cokernel and support dimension. The coherent generic-free-neighbourhood results concern sheaves over integral schemes and do not give the universally injective map over the local base or flatness of its cokernel at the specified point. No exact project declaration was found.

## WANTED

None. The required sources are present.

## Findings and corrections

Read Stacks flat.tex, Tag 05I3 (lemma-induction-step), including its existence construction and (1) implies (2), and Tag 05I5 (proposition-finite-type-flat-at-point), first proof, induction step. The item is a faithful algebraic extraction of those paragraphs. The source's existence argument can use a subset of any fixed finite generating list: their images span the residue-field tensor product and finite greedy elimination selects a basis. This was written out explicitly, including the empty list.

The imported item had no proof. The delivery supplies six steps. The substantive universal-injectivity argument is already the statement of lem-trf-local-generic-basis-universal-injective, whose hypotheses match exactly. This is strictly less than the item: it assumes a generic-basis map, does not construct one from prescribed generators, and does not assert support closedness or dimension drop. Therefore it is reused rather than duplicated. Tensor right exactness and the finite-module support-annihilator theorem already exist as Mathlib leaves. The dimension lemma is also already present and is reused as a generic topological tool.

The nearest blueprint ancestor is lem-trf-local-term-locality. I read its statement and proof in literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/, and the chapter and unit records. This item serves an existing supporting algebra branch beneath the locality node, through the flat-point and finite-type-flat-etale-neighborhood nodes. The latest locality proof itself follows contracting correspondences, not an explicit algebra proof of 05I5; the blueprint attribution therefore identifies the existing supporting branch and does not claim that the latest locality proof contains the algebra argument. No unit or chapter route is changed. Blueprint searches for “generic free”, “cokernel”, “universally injective”, and “support dimension” found no imported node stating this item. Its same_as stays empty.

## Mathlib searches

Ran five searches through the required msearch.py wrapper: LeanFinder twice with different wordings, Loogle with Module.Flat, Module.Finite, Ideal.IsPrime, grep for generic basis/cokernel flat/universal injectivity, and LeanSearch. All five succeeded and are recorded exactly in searches.jsonl and appended to the item's existing mathlib_searches; earlier searches were retained. Read the results. In FreeLocus.lean at lines 343–356 the rank-at-stalk constancy lemma uses global flatness of M over its coefficient ring. In LocalRing/Module.lean at line 395 the finite free basis theorem needs finite flatness over that ring. Neither applies with only N_q flat over A. In Algebra/Module/FinitePresentation.lean at line 510, exists_notMem_bijective requires finite presentation of the target N; this item assumes only finite generation. The support and quotient hits prove proper subclaims, not the whole statement. The generic-freeness/free-locus hits do not give universal injectivity over A or the cokernel's A-flatness. No search is recorded as unavailable or as a match.

## Not duplicates

No nodes are created. The existing 05I3 implication, tensor right exactness, finite-module support-annihilator theorem and irreducible-open-complement dimension bound are reused. The generic-basis-base-open node has a general base and a finitely presented module, and gives injectivity only after shrinking the base; it is not the present local statement and is not used.

## Review by NH

I checked delivery-errors B–E against the node and the sources. There are no new statement-only nodes requiring individual source or notion audits. The original statement introduces all its objects, defines geometric integrality explicitly, and defines cokernel and universal injectivity inline. Its definition dependencies were opened and read; they define the notions actually named. The statement is not disputed and has not been weakened.

Step 1 uses the actual statements of the residue-field, module-localization, tensor-product and affine-spectrum definition nodes. The closed fibre is the quotient because A is local; I give the two inverse tensor/quotient maps. Its domain property is an explicit hypothesis, so mB is prime. Localizing this quotient at all nonzero elements identifies the residue field at mB with its fraction field. The generic-point assertion is checked directly on basic opens; this is elementary, not an invocation of an unstated geometric-integrality theorem.

Step 2 uses precisely the finite-generation and tensor-product definitions: expansion of pure tensors proves that the given generators span after tensoring. Finite elimination retains an independent spanning sublist, giving the requested map from B^r. It makes no flatness or finite-presentation assumption on N. I checked V=0: the retained list is empty and the zero-rank clause is respected.

Step 3 cites only lem-trf-local-generic-basis-universal-injective. I read its complete statement, source, proof and review. Its conclusion explicitly says both R-universal injectivity and flatness of the localized cokernel. Its hypotheses are verified in the step one by one: local base, flat finitely presented algebra with all fibres geometrically integral, finite module, q over m, flat N_q, and the generic residue-field isomorphism. No proof of that node is being used as an interface, and its dependency closure does not contain this item.

Step 4 uses the finite-generation definition to pass the same generators to the quotient. It uses the actual two-sided tensor right-exactness statement of lem-weil-pbc-tensor-right-exact (Stacks 00DF, algebra.tex lemma-tensor-product-exact, read at lines 1994 onwards). The injective first arrow comes from step 3, not from right exactness. Evaluating on A proves injectivity before base change, and evaluating on an arbitrary A-algebra proves the entire short exact sequence after base change. No global A-flatness of N or Q is asserted or assumed.

Step 5 again uses tensor right exactness, now over B, to kill the cokernel after tensoring with K. I wrote the actual mutually inverse maps identifying Q tensor_B K with (Q/mQ)_(0), using the tensor and localization definitions, so “transport” hides no theorem. The finite-module support-annihilator statement applies to the commutative ring C and the finite C-module T, with no Noetherian hypothesis. I read its statement and Stacks 00L2 (algebra.tex lemma-support-closed): it says exactly that the support is V(Ann(T)) and therefore closed. This supports closedness rather than an inference from finite presentation or flatness not available here. The zero generic stalk then proves properness.

Step 6 uses the complete statement of new-node-irreducible-open-complement-dimension. Its hypotheses are satisfied with X=Spec(C), d=n and U the complement of the closed support: X is nonempty and irreducible, U contains the generic point, and dim X=n is assumed. The conclusion gives precisely an integer bound e<n unless the support is empty. I read the existing node's proof and its project declaration in WeilConjectures/Topology/IrreducibleOpenComplementDimension.lean, which writes the chain-extension argument in full. Dimension at a point is the minimum of neighbourhood dimensions in def-kun-dimension, so it is at most the dimension of the whole support. For n=0 the nonempty alternative would give a natural number e<0, which is impossible. This also works when the support is empty to begin with. I declared the off-unit dimension node as a generic tool in split_report.tool_uses, with the reason; no top-level tool_uses field was set.

Small cases: N=0 gives r=0 and Q=0; over A=k and B=k[t], N=B/(t) gives r=0 and support a closed point of dimension zero, strictly below one; N=B gives r=1 and zero cokernel; B=A with a finite A-flat N gives a basis and empty support as n=0 requires. A zero ring cannot satisfy the required nonzero integral closed fibre with q over m. These cases show why neither positive rank nor nonempty support is tacitly assumed. No theorem about a field extension or a smooth algebra is being substituted for the stated hypotheses.

Every uses entry has a verbatim quotation in citations.json. All cited statements were opened. All dependency closures were checked not to lead back to the item. Each step has fewer than 700 characters, so no step exceeds the 2000-character long-step review threshold. The two elementary steps contain explicit constructions; the remaining steps cite each non-elementary result. There is no SGA reference. The server review_split check passed before this report was written. The final dry run and push follow.

## Unfinished work

None within the requested one-level split. No Lean was written and no compiler or build tool was run.
