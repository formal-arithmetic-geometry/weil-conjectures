# lem-trf-colimit-unramified-algebra — Q08

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-colimit-unramified-algebra.json`: statement node, now split in six steps; no Mathlib match for the full finite-stage descent assertion.
- `citations.json`: verbatim statements for the three step/node citations (steps 2, 4, 5).
- `report.md`: this report. The search command maintains `searches.jsonl`.

There are **0 new nodes and 0 new Mathlib leaves**. The existing Mathlib leaves for differentials and their base change and the existing Lean-closed tensor-colimit theorem suffice. The unit is not edited: this item is not its key node.

## Attachments

No attachment for the item. Searches for its exact blueprint tag, colimit/unramified phrases, and differentials/colimit phrases in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration asserting the item. The existing dependency `TensorProduct.directedColimitBaseChangeElementwise` belongs to `lem-weil-pbc-directed-colimit-base-change-elementwise`; its existing audit is `closed`. This is reuse of a recorded attachment, not a new attachment request.

## WANTED

None. All mathematical sources used are in `literature/stacks-project/algebra.tex`.

## Corrections and route

The imported statement and Stacks 0C4F agree in hypotheses and conclusion. I made the domain of the notation explicit: define B_i and C_i **for i >= i_0**. There is no given A_{i_0}-algebra structure on A_i for other indices. This is an indexing clarification, with no added mathematical hypothesis and no weakened conclusion. The original proof was empty.

I read the chapter and unit records and the current `main-20261015` local-term node and unit text. Their current contracting-correspondence route has superseded the historical nearby-duality/alteration route in this item's ancestry. The item's existing historical blueprint ancestry is retained honestly; this delivery does not identify its algebra lemma with a new clause of the revised local-term theorem. It supplies exactly the affine algebra fact requested by its parent unramified-limit-descent node. No chapter, unit, or parent is edited.

The source 0C4F identifies the directed colimit of differentials by 031G. Instead of adding a general differentials-colimit node, step 4 uses the already existing 00RV base-change leaf to express these particular differentials as scalar extensions of Omega_{C_0/B_0}. Step 5 uses the already existing elementwise tensor-colimit theorem to kill each of the same finitely many generator differentials. This is the source's finite-generator argument, with its colimit sentence implemented by existing nodes; no unit step or theorem is replaced.

## Searches and reuse

Read the existing item's four Mathlib search records. Also ran five logged searches: LeanFinder for the full unramified descent statement; Loogle for `Algebra.Unramified`; grep for unramified/colimit and unramified/direct-limit patterns; LeanSearch for filtered-colimit descent; and a second LeanFinder phrasing in terms of vanishing of differentials after scalar extension. All services returned successfully. Loogle found unramified base change, composition and faithfully flat descent, but none descends along an arbitrary directed colimit. The second LeanFinder found `KaehlerDifferential.finite`, which supplies only finite generation, not finite-stage vanishing. LeanSearch's finite-presentation Hom-descent result has a different conclusion and stronger finiteness assumptions. Read the local source of `Algebra.Unramified` and `Algebra.Unramified.baseChange` (Unramified/Basic.lean, lines 358 and 395); these do not assert this item. No match for the item was declared.

Searched the whole DAG for 0C4F, 031G, 00RV, 00RZ, differentials generators, and tensor/elementwise colimit lemmas, and ran `tools/blueprint_refs.py ancestor` plus whole-blueprint searches for `differentials` and `colimit`. This found the existing base-change and tensor-colimit facts, avoiding duplicate nodes. The nearest blueprint ancestor remains `lem-trf-local-term-locality`; no blueprint node states this same algebra descent assertion.

## Not duplicates

No new nodes. In particular no new node was made for finite generation of differentials, the polynomial calculation, tensor associativity, vanishing of a finite set at a common later stage, or the 031G colimit theorem specialized to this scalar-extension family.

## Review by Q08

I read Stacks Tag 0C4F (`lemma-colimit-unramified`), including its full proof at algebra.tex 47571 onward, and checked the hypotheses against the item. The source only assumes finite type of C_0 over B_0: finite presentation, flatness of any transition, injectivity of a ring coprojection, and Noetherianity are unnecessary and are not used. I read the differential presentation and universal property (07BK and 00RO), the generator calculation in 00RX, the full base-change statement and proof 00RV, and the module colimit statements 00D6, 00D7, 00DD. There are no new nodes requiring separate source checks.

Step 1 uses just finite algebra generation and the definition of a tensor product. Expanding a polynomial expression for each c in a finite sum of tensors explicitly gives generation of every C_i over B_i. The coefficient b is mapped through phi_0 into C_0; a tensor coefficient a tensor b lies in B_i as required. This justifies finite type at every stage, rather than incorrectly trying to descend finite type from the limit.

Step 2 cites `def-weil-pbc-kahler-differentials`. I opened its statement: it gives additivity, the Leibniz rule, vanishing on the base ring, and the presentation as a quotient of the free module on [c]. These are exactly the inputs used. The monomial formula is written out, with the sum restricted to positive exponents so no negative powers appear. Additivity and the presentation imply generation by the differentials of the chosen algebra generators. This is an elementary calculation from the definition, not an uncited finite-generation theorem.

Step 3 is elementary tensor balancing. Both the base-change ring isomorphism and the module tensor isomorphism have explicit maps and inverses. In the ring map, b acts on c through phi_0. In the module map, c acts on Omega_{C_0/B_0} through its C_0-module structure. Each map therefore has the displayed scalar rings, and both inverse identities are checked on spanning pure tensors. This step applies also to the colimit ring A and does not use any faithfulness assumption.

Step 4 cites `lem-weil-pbc-kahler-differentials-base-change`. I opened its complete statement: it gives the isomorphism for arbitrary commutative ring maps, its generator formula, and its equivalent C_T-module form. Substituting R=B_0, R'=B_T, S=C_0, S'=C_T is legitimate by step 3, and gives precisely the isomorphism needed. The formula sends 1 tensor d x_r to d(1 tensor x_r), so vanishing at the limit gives the desired zero elements of A tensor M_0 by injectivity. We do not assume M_0 is finitely presented or finite as an A_{i_0}-module; it is only finite as a C_0-module.

Step 5 cites `lem-weil-pbc-directed-colimit-base-change-elementwise`. I opened its statement, existing proof and closed audit. Clause (2) applies to an arbitrary A_{i_0}-module, exactly M_0 here, and kills an element at a later stage when its tensor image is zero at the ring colimit. We apply it separately to finitely many elements of A_{i_0} tensor M_0, then use directedness to take a common upper bound. The tensor transition formula is written explicitly, so zero at j_r stays zero at i and the same generator differential is killed. This existing generic tool is from another unit but is already Lean-closed; no undeclared open proof route is imported.

Step 6 uses the two results already proved: finite type from step 1 and zero differential module from steps 2 and 5. A generated module with all its generators zero is zero. This proves both clauses of the stated unramified condition, not merely formal unramifiedness.

I checked delivery-errors B1-B10: no new unsplit statements or duplicate nodes, statements self-contained, existing notions cited, TeX singly escaped after JSON decoding, exact Stacks tags/labels, no Mathlib leaf claim or attachment beyond the evidence, and blueprint ancestry retained. For C1-C8 each non-elementary input is the statement of its cited existing node, not an argument hidden in that node's proof; citations.json copies each cited statement verbatim. All cited nodes are unmerged. For D1-D5 no new node restates the item or any of its clauses: the six steps carry the entire finite-generator argument. For E1-E7 I verified all scalar rings, arbitrary directed transitions, the correct base-changed ring C_i over B_i, and the explicit transport of the generators.

Edge cases checked: m=0 (C_0 is generated by the image of B_0 and all differentials vanish already), C_0 the zero ring, a one-element directed set, and noninjective transition maps which kill all of the limit ring. The argument works in each case. An arbitrary index i_0 need not be the least element of I: only its upper tail is used, and the existing tensor-colimit node explicitly permits any initial index. No proof step exceeds 2000 characters, and none hides an additional non-elementary comparison. No SGA source is used. No Lean was written or compiled; no git command or write was run in either read-only repository.

## Unfinished work

None in the mathematical split. New nodes: 0. New Mathlib leaves: 0. Required server dry run and delivery are run after this report is written.
