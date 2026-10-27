# Q134: lem-sfb-finite-hopf-dual-pairing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-hopf-dual-pairing.json — item, statement unchanged, split into eleven explicit evaluation/word-induction steps; no whole-item Mathlib match.
- citations.json — fourteen step/node entries, quoting verbatim the statements read.
- report.md — this report.

No new nodes and no new Mathlib leaves. prepare.py is a sandbox-only JSON-writing aid; searches.jsonl is the search command's original log.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for Hopf, bialgebra and primitive pairing notions. There is no declaration stating this item. Existing Fourier convolution declarations concern sheaves and do not apply. The old upstream reference was also searched read-only, without finding an attachment.

## WANTED

None for this split. Milne's Algebraic Groups PDF is present and was read at printed pp.65–66 and 222–223. His references to Demazure–Gabriel are not used as unexplained lemmas. No Stacks tag was used: the Hopf-algebra facts here are the displayed algebra calculations, rather than a theorem assigned a Stacks tag.

## Corrections and scope

The item was unsplit with no proof; there was no previous sandbox item or report to preserve. Its statement is correct and is retained literally. Milne Proposition 11.35 gives the finite-dimensional field construction, not this general base-ring generator criterion. The proof_origin is consequently agent, and the source identifies the generalization honestly. I made all Hopf axioms, the unit check in the primitive criterion, the word induction, antipode compatibility, and scalar-extension compatibility explicit.

In particular the end of the statement is interpreted exactly as its qualification says: pairings are extended by the formula <u tensor b,v tensor c> = uv<b,c>. It does not claim dual base change for arbitrary C. No finiteness, projectivity or flatness of C, and no flatness of T, is added. Cocommutativity is needed only for commutativity of the dual algebra. No source-route change is made.

The existing finite-coalgebra-dual-base-change node is field-only and does not state the full item. I reused its two generic prerequisites instead: lem-sfb-finite-free-tensor-dual and lem-sfb-convolution-linear-map-algebra. Both are existing Mathlib leaves in this unit. Hence there is no off-unit tool use. I did not create nodes restating individual clauses or elementary tensor calculations.

## Searches and duplicate checks

Read the existing recorded item searches and their hits; ran fresh logged Q134 LeanFinder, Loogle, grep and LeanSearch queries, with a second semantic phrasing. Read Mathlib/LinearAlgebra/Contraction.lean:440–463 and Dual/Lemmas.lean:1087–1101 for the tensor-dual map, Coalgebra/Convolution.lean:55–68,174–215 for convolution, and HopfAlgebra/Convolution.lean for the returned antipode hits. The hits give components, not the whole assertion. Each fresh query in mathlib_searches is copied from searches.jsonl with its original query and result. No unavailable service was called a negative result.

Searched the whole DAG and latest blueprint by Hopf, finite dual, primitive pairing and convolution, and ran blueprint_refs.py ancestor and search. The ancestor command reports None; the inherited null ancestor and full via chain are retained. The latest-blueprint Hopf hits concern algebraic-group geometry and do not state this item. Existing finite-dual-hopf-module is about an action/coaction on the dual of a commutative field Hopf algebra, not dualizing a finite free cocommutative algebra. No new nodes means there are no new/existing pairs requiring a Not duplicates section.

## Review by Q134

I read coord/delivery-errors.md B–E whole and compared the eleven steps with the statements of all four cited nodes, not their proofs. I also read the chapter, unit, GOAL, the three-level restrictions in SETUP, the worker role and stage-1 contract. The inherited route is the finite-dual supporting input to Milne's height-one integration construction. No unit/chapter or repository files were changed.

Step 1 uses free-module basis coordinates, convolution associativity and unit, and precisely the tensor-dual isomorphism for finite free modules. Its B satisfies both finite-free hypotheses. The dual basis proves that A is finite free as well; this is not inferred from a field-only lemma. Step 2 uses the tensor-dual evaluation formula and writes the product-basis coefficient test and coassociativity/counit calculations. Steps 3–4 use the same formula to test the bialgebra and antipode identities, with the tensor order displayed; they do not assume B commutative. Step 5 uses basis coordinates and generation by pure tensors to give an actual inverse for the scalar comparison, then checks its Hopf operations. The finite-free hypothesis survives any scalar extension by that displayed basis, so the tensor-dual leaf can be applied over T without a flatness assumption.

Step 6 uses convolution for an arbitrary coalgebra C, just as its cited statement explicitly permits, and the finite-free tensor-dual injection only for B. It obtains the coalgebra and counit maps from the algebra property of r. Step 7 has no non-elementary citation: evaluate the generator condition at (1,1), subtract in the ring, and compare two algebra maps on words and their finite linear combinations. Step 8 uses the convolution formula to carry out the full product step in word induction, displaying all four tensor factors and the only commutation, in R. It does not assume the convolution algebra C* is commutative. Step 9 uses the associative convolution algebra with values in A and writes the left/right inverse uniqueness argument, proving rather than silently invoking antipode compatibility. Step 10 checks the inverse transpose by the defining coalgebra equality. Step 11 spells out naturality by precomposition in each variable and the scalar-extended pairing; it uses only tensor balancing and pure-tensor generation from its cited definition. No step takes a result from the proof of a cited node.

I checked R=0, B=R and P empty, T=0, and the characteristic-p primitive example B=R[x]/(x^p) in characteristic p with its usual Hopf structure. In the first two degenerate cases the empty/one-element basis arguments and word-span arguments still apply. Subtraction at the unit does not divide by 2, so characteristic 2 introduces no exception. An infinite or non-flat C is used only through its coproduct's finite tensor presentations; its dual is never identified with the dual of a scalar extension. The antipode computations require neither an anti-algebra identity for S_B nor an unproved uniqueness theorem. Each step is under 2000 characters. In particular no long step hides an additional comparison lemma.

The B checklist is satisfied without new nodes; C is checked by verbatim citations, the absence of cycles below the existing generic leaves, and no off-unit citation; D is addressed by writing the construction and induction instead of replacing clauses by new statements; E is addressed by the base-ring, unit, tensor-order and degeneracy checks above. Nothing remains unfinished. The server dry run and direct delivery are the remaining mechanical checks.
