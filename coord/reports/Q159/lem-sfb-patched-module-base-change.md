# Q159: lem-sfb-patched-module-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-patched-module-base-change.json`: statement, now split, with eight proof steps. The statement is unchanged. Mathlib searches found no exact theorem or one-line specialization for the whole item.
- No new nodes and no new Mathlib leaves. The proof reuses `def-weil-pbc-module-tensor-product`, `lem-weil-pbc-tensor-over-quotient-ring`, and `lem-weil-pbc-tensor-right-exact`, all existing Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the nine step/node citations. `searches.jsonl` and `search-0.txt` through `search-4.txt` preserve the actual Q159 queries and complete returned hits.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag, item id, patching/module terminology, fibre/fiber product terminology, and 07RU. No declaration states this item. Unrelated Milnor-sequence and geometric gluing hits do not state it.

## WANTED

None. The source and all generic algebraic inputs are in the read clone.

## Problems in the imported material

The imported item had no proof. Its statement accurately captures the final assertion of Stacks Tag 07RU; no statement dispute or added hypothesis is needed. In the Stacks proof, observation (11) says `l in K` when naming generators in the tensor product of N'. The well-typed submodule there is L, as observation (12) itself says. Step 6 uses L and explicitly derives the two generator families from right exactness. The local typo changes no assertion of the item.

The inherited blueprint ancestry has `from.node=null`; `tools/blueprint_refs.py ancestor lem-sfb-patched-module-base-change` confirms this. I preserved that ancestry and its exact, already populated `from.place` and `via`. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, not an older snapshot. This item is the supporting module calculation in the inherited deformation/alteration chain, not a restatement of its unit. The stored unit record is historically filed in sec-six-functors while this item's chapter is sec-six-functors-basics; no chapter or unit record was changed.

## Unfinished

No mathematical part remains. Delivery is subject to the required server dry run and independent maintainer review.

## Not duplicates

No new nodes were created. The whole-DAG search by 07RU/08KH found the item and related scheme, algebra, and invertible-patching nodes. I read `lem-sfb-fibre-product-algebra-flat-presentation`, `lem-sfb-scheme-pushout-flat-patching`, and `lem-sfb-finite-pinching-invertible-patching`: they concern flat algebras, schemes, or invertible sheaves and do not give recovery of arbitrary modules. The existing generic tensor quotient and right-exactness nodes supply exactly the tool statements needed here, so no specialized replacement nodes were introduced. Whole-blueprint searches for `module-over-fibre-product`, `patching`, `tensor quotient`, and `fibre product`, and a search of the latest blueprint text for the module-patching assertion, found no blueprint node stating this item in another form; `same_as=[]` is retained.

## Mathlib searches and candidate assessment

The five Q159 queries are recorded verbatim in the item and in the search log: LeanFinder twice with distinct phrasings, Loogle, grep, and LeanSearch. All services answered. The searches found generic base-change composition/cancellation, scalar extension adjunctions and faithfully flat descent, geometric pullbacks, and a tensor-kernel comparison assuming flatness. Those do not give arbitrary-module patching over a ring pullback as a one-line specialization. I read the base-change interfaces in `Mathlib/RingTheory/IsTensorProduct.lean` and the flat-kernel interfaces in `Mathlib/RingTheory/Flat/Equalizer.lean`; they assume the base-change or flatness property rather than proving the required patching result. I retained all earlier Q49 search records as provenance and appended the actual Q159 results. The three reused Mathlib leaves were read as DAG statements, including their recorded declaration locations; no new claim of a Mathlib match is made.

## Review by Q159

I read Situation 08KH and the complete statement and proof of Tag 07RU, `lemma-module-over-fibre-product`, in `literature/stacks-project/more-algebra.tex`, including all thirteen observations. The split follows these observations and adds the explicit naturality check. There are no new nodes requiring separate source reviews. I also opened the full statement of every cited node: the tensor-product definition states both its bilinear universal property and generation by pure tensors; tensor-over-quotient-ring gives (1) the ideal quotient tensor formula and (2) cancellation of scalar restriction for modules over that quotient; tensor-right-exact gives exactness after tensoring an exact sequence whose last map is onto, in either tensor variable.

Step 1 directly checks the two surjections and kernels in coordinates; it cites no theorem. Only the stipulated surjectivity of A' to A is needed, and no surjectivity of B to A is assumed. Step 2 uses the tensor definition's pure-tensor generation to expand the inverse gluing image, then lifts only finitely many elements through the two known surjections; its remainder belongs to K and has the explicit lift (0,k). This is why generation upstairs does not use Nakayama. Step 3 writes each element of IM' as a finite sum and substitutes the expression from step 2, proving JN'=L by the displayed coordinate products; no extra patching theorem is hidden here.

Step 4 takes exactly clause (1) from tensor-over-quotient-ring, with base ring R and ideal J. The identifications R/J=B and N'/L=N were proved in step 1 and JN'=L in step 3. The tensor definition supplies interchange of factors by its universal property, and the generator formula identifies the isomorphism with the map in the statement. Step 5 uses that same universal property for the displayed balanced bilinear map and step 2 for surjectivity; no exactness of tensor on the left is asserted.

Step 6 takes exactly the two-sided right-exactness assertion from tensor-right-exact. Its two exact sequences are L to N' to N to zero and I to A' to A to zero. Their surjectivity hypotheses were checked in step 1 or are assumptions of the item. I wrote how to lift generators from the second kernel and reduce the remainder to the first kernel, so the description of the composite kernel is justified. Tensor generation is the quoted clause of the definition node. Clause (2) of tensor-over-quotient-ring is applied with quotient R/J=B and modules N and A; J annihilates both. This identifies the final quotient tensor with N tensor_B A, where phi is an isomorphism by assumption. Thus no flatness hypothesis is smuggled into the kernel computation.

Step 7 uses only JN'=L already proved and the balancing/additivity relations from the tensor definition. I checked both families of kernel generators separately: l tensor a' is reduced using an expansion l=sum j_s x_s, and x tensor i uses the actual scalar (0,i) in R. The elements i_s a' stay in I, even though R to A' need not be surjective. Hence all resulting tensors have first factor in L. Their gamma images are their K-coordinates in the actual submodule IM' of M'; zero image forces the coordinate, and therefore the tensor, to vanish. This is an explicit injectivity argument, not an appeal to a missing flatness or gluing lemma. Step 8 uses the tensor definition's generation clause to check each naturality square on pure tensors, writing both compositions; compatibility with phi ensures that the coordinate pair map lands in the next fibre product.

I tested the boundary cases: I=0 (R=B and N' is the graph of N to M'); A=0 (independent product rings and modules); A'=0 (forcing A=0 and M'=0); zero N or M'; and non-nilpotent I, for example Z to Z/2 with B=Z/2 and M'=Z or the nonflat module Z/4. In particular N=0 does not force M'=0 when M'=IM': taking A=0 and I=A' shows why a Nakayama-based proof would fail. The displayed calculations still work. None uses finite generation, Noetherianity, flatness, or nilpotence. I reviewed B through E of delivery-errors in full: there are no new statement-only leaves to disguise a clause, no reliance on a cited node's proof rather than its statement, and no uncited non-elementary step. Every proof step is below 2000 characters; the two generic non-elementary inputs are separately cited. The complete item argument remains in its own proof, and the only source correction is the K/L typo described above.
