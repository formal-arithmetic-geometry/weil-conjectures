# Stage-1 worker report: Q22

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-relative-diagonal-finite-type.json`: item, statement unchanged, split into four steps using existing nodes; no Mathlib match.
- `citations.json`: eight verbatim statement witnesses, one for each step/node citation.
- `searches.jsonl`: the five actual searches run through the prescribed msearch command.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, relative diagonal / finite-type terminology, algebraic stacks, and Isom-space terminology. No declaration proves this algebraic-stack statement. Scheme diagonal results are insufficient, and none has been presented as an attachment.

## WANTED

None. Every source used is present locally.

## What needed repair

The item was statement-only. Its statement agrees with Stacks Tag 04XS, parts (1) and (2), including the scheme-test formulation in the proof. No statement dispute or correction is needed. The split now gives the concrete fibre-product argument rather than treating representability or the local-finite-type conclusion as an unexplained lemma.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` returns None. I preserved this maintainer-owned ancestry and the existing detailed `from.place`/`via` chain. I read the latest blueprint direct-images proof, clause (3), as well as the chapter and unit records. This prerequisite lies below the imported alteration/moduli chain; nothing at the chapter or unit level is changed. Searches `blueprint_refs.py search 'relative diagonal'` and `search '04XS'` found no blueprint statement of this result (the former hit concerns fixed loci of correspondences). Broader diagonal, Isom, and locally-finite-type searches were also made; the existing DAG has the smaller supporting facts used below.

## Not duplicates

No new nodes are created. In particular I reused `lem-sfb-stack-isom-space-locally-finite-type` (04XR), `lem-sfb-space-lft-cancellation` (0462), `lem-trf-space-fibre-products-etale-covers` (02X2), and the algebraic-space base-change case of `lem-sfb-stack-finite-type-calculus`. Creating replacements for these facts would duplicate the DAG. The source/definition nodes used are likewise existing nodes.

## Review by Q22

I read the complete proof of Stacks 04XS (`stacks-morphisms.tex`, `lemma-properties-diagonal`), the preceding 04XR statement and proof, 0462 (`spaces-morphisms.tex`, `lemma-permanence-finite-type`), 03XH (`lemma-base-change-finite-type`), 02X2 (`spaces.tex`, `lemma-fibre-product-spaces`), and the compatibility paragraph before the stack definition of local finite type and its base-change lemma 06FU. These sources give exactly the route used here: Isom spaces, the fibre square over the chosen isomorphism, cancellation, and base change. There are no new-node sources to review.

For step 1 I opened the full statements of `def-sfb-stable-pointed-moduli-groupoids`, `def-trf-algebraic-space`, and `lem-sfb-stack-isom-space-locally-finite-type`. The first explicitly identifies maps from a scheme with fibre objects and defines the triples in a 2-fibre product. The second defines maps of algebraic spaces as natural transformations. The third states that the Isom sheaf of ANY two objects over a scheme in an algebraic stack is an algebraic space locally of finite type over that scheme. I apply it separately to X and Y, both algebraic stacks by hypothesis, over the same T. The map on Isom sheaves is induced by the given functor f and is over T. Nothing assumes f itself is locally of finite type.

For step 2 I opened `lem-trf-space-fibre-products-etale-covers`: its first clause gives the sheaf fibre product as an algebraic space, without imposing etaleness on either map. I use only that clause. The triple and arrow descriptions come from the cited groupoid definition. I checked the orientation: for an arrow from (z,z,id) to (x,x',alpha), the compatibility is f(v)=alpha f(u); hence beta=v u^{-1} maps to alpha, not its inverse. Between two triples with the same beta the unique arrow is (u')^{-1}u. This proves the equivalence with the discrete fibre sheaf, including automorphisms and compatibility with pullback, rather than invoking an uncited 2-Yoneda lemma. Forming a fibre product is the only previously cited existence theorem in this step; the explicit inverse constructions are elementary. No standalone comparison lemma is hidden here.

For step 3 I opened `lem-sfb-space-lft-cancellation`. It states cancellation for morphisms of arbitrary algebraic spaces over S with no separation, finite-type or scheme-representability assumption on the second arrow. With X=I, Y=J, Z=T, the composite is the structure map I to T proved locally of finite type in step 1. Thus every hypothesis is supplied. I did not misapply the scheme-only cancellation node.

For step 4 I opened the complete `lem-sfb-stack-finite-type-calculus` statement. It states arbitrary-base-change stability, tests representable maps on algebraic-space scheme base changes, and explicitly identifies the stack and ordinary algebraic-space notions. Only its algebraic-space case is used on q:I to J and T to J. Algebraic spaces are within the Deligne--Mumford scope: a sheaf is a discrete stack, its diagonal is representable and its defining etale chart is a DM atlas. Consequently the lemma is not being applied to arbitrary Artin stacks under DM-only hypotheses. The base change map T to J is a section and need not be smooth, which is why the arbitrary-base-change assertion is used. The groupoid definition explicitly defines representability by all scheme tests. The local-finite-type convention is exactly the representable/chartwise convention of the statement, so the conclusion includes every requested test T,t. The copied witness includes both the base-change and ordinary-space compatibility clauses.

I checked the small cases: if f is an identity, q is the identity Isom map and its fibre over alpha is T; if the required lifts of alpha do not exist, the fibre is empty, still an algebraic space locally of finite type. Nontrivial stabilizers are retained in I, and the arrow calculation shows the diagonal fibre has no leftover automorphisms. No quasi-compactness, finite type, separatedness or finiteness of stabilizers is assumed or concluded. An infinite discrete smooth group illustrates why upgrading local finite type to finite type would be unjustified; no such upgrade occurs.

Against delivery-errors B--E: the unchanged statement is self-contained through its definition dependencies; all source tags were checked against the local tag map. There are no new nodes, provisional proof sketches, counterfeit Mathlib leaves, or duplicate definitions. Every non-elementary input is the statement of a cited existing node, and each citation has a verbatim witness independently checked as a substring. Proof dependencies are exactly the union of uses. I traversed the statement/proof dependency closures of the supporting nodes and found no return path to this item. The proof has no induction, unsupported transport, hidden choice of a chart, or omitted hypothesis. Every step is under 2000 characters (569, 909, 359, 580); together they give an assembly proof under 3000 characters. No clause has been moved wholesale into a new node. All substantive supporting facts were already in the DAG.

I ran LeanSearch, Loogle, grep, and LeanFinder, then a second semantic phrasing for fibres of the Isom map. All five services answered successfully; their exact queries and returned names are recorded in the item's added search records and searches.jsonl. The hits are scheme diagonal/cancellation/base-change theorems or ordinary categorical representability, not the algebraic-stack assertion. I read the grep hit `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:126` and the ordinary categorical `Functor.relativelyRepresentable.diag_iff` at `Mathlib/CategoryTheory/MorphismProperty/Representable.lean:670`; neither supplies this node. Existing inherited search records are retained. No searches were invented and no compiler, Lake, local DAG checker or forbidden source route was used.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own independent proof obligations. The required server dry run and direct delivery are performed after writing this report.
