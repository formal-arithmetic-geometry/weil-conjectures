## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-separated-fp-composition.json: item, statement, split into six proof steps; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every node used in every step.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and separated/finite-presentation/algebraic-space terminology. Scheme declarations do not state these arbitrary algebraic-space assertions. The existing Sheaf algebraic-space definitions are not completed proofs of this item.

## WANTED

None. All mathematical source material is present in literature/stacks-project.

## Corrections and scope

The imported conclusions are correct. I corrected literal doubled TeX backslashes in the item's statement, and replaced its abbreviated topological gloss of quasi-compactness by the precise all-quasi-compact-space-base-change definition of spaces-morphisms Tag 03HE (definition-quasi-compact), using the existing node lem-sfb-space-quasicompact-fppf-local. This records the intended Stacks notion for arbitrary nonrepresentable maps; no conclusion or separated/local-finite-presentation hypothesis is changed. I do not identify mere quasi-compactness of an arbitrary continuous point map with this base-change-sensitive definition.

The item had no proof. The proof now writes out the diagonal factorization, base-changed diagonal, scheme tests of representable closed immersions, transitivity for quasi-compactness, and compatible scheme presentations. In particular, none of the four clauses is transferred to a new node. The inherited blueprint provenance is retained. I read the latest blueprint direct-image proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md: its current (3) is compactification assembly and no longer spells out the older alteration subargument named in the inherited provenance. This split remains a generic prerequisite of the historical Hom/moduli branch; it changes no chapter/unit route or realization record.

## Mathlib and duplicate searches

Read the inherited five Mathlib search results, then ran and recorded two semantic phrasings, Loogle, grep and LeanSearch through the required msearch.py command. LeanSearch and the other services returned normally. The hits are Scheme.IsSeparated composition/base-change and LocallyOfFinitePresentation composition, including Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:80, whose source explicitly quantifies X,Y,Z : Scheme. They do not apply to arbitrary algebraic spaces, so the item is not a Mathlib leaf. All appended records use the exact logged tool/query, actual returned names and date. The inherited searches are retained as historical research.

Searched the entire DAG by source tags 03KL, 03KQ, 03XQ and by algebraic-space, etale-locality, quasi-compactness, closed-immersion and composition terminology. Searched the whole blueprint using blueprint_refs.py for finite presentation, closed immersion, etale local, separated, and the item/scheme-composition title. The resulting existing scheme and presentation nodes suffice; no new node is justified. Generic off-unit tools are declared in split_report.tool_uses. I checked the cited nodes' dependency closure cannot reach the item before writing the proof.

## Not duplicates

No new nodes. Existing presentation, scheme locality, closed-immersion composition and scheme local-finite-presentation composition nodes are reused.

## Review by Q154

I read spaces-morphisms.tex Tags 03KL (lemma-base-change-separated), 03KQ (lemma-composition-separated), and 03XQ (lemma-composition-finite-presentation) with their complete proofs. I also read the intervening magic-diagram statement and proof, Tag 03MJ (lemma-local-source-target), remark-composition-P, Tag 03HE (definition-quasi-compact), Tag 03HG (lemma-composition-quasi-compact), and Tag 03XP (definition-locally-finite-presentation). In morphisms.tex I read Tag 01QS (lemma-composition-closed-immersion) and Tag 01TR (lemma-composition-finite-presentation). In descent.tex I read remark-list-local-source-target, which explicitly includes local finite presentation. There are no new-node sources to review and no SGA source is used.

Step 1 uses the statement of lem-trf-space-fibre-products-etale-covers: fibre products exist in algebraic spaces with their universal property. It does not take anything from its proof. I checked both diagonal identities on sections: the middle common Y-section is uniquely forced, and equality is preserved by restriction. This is a routine universal-property calculation; no separatedness assumption or representability of f or g is smuggled in.

Step 2 uses the full definition of representability in def-trf-algebraic-space and the scheme definition def-weil-closed-immersion, plus exactly the statement of lem-weil-pbc-closed-immersion-comp. A scheme test of a pullback is already a test of the original closed immersion. For composition, the intermediate base change is a scheme because the second map is representable; the first test therefore is also a scheme closed immersion. This checks the hypothesis of the scheme composition node. Applying this to step 1 proves both separatedness clauses. No general algebraic-space separatedness theorem is cited as a black box.

Step 3 uses the definition and base-change assertion of lem-sfb-space-quasicompact-fppf-local and the fibre-product universal property. Given a quasi-compact space T over C, first B_T is quasi-compact and then A times_B B_T is quasi-compact. This is the whole omitted transitivity argument of 03HG, written in the step rather than made a node. The same argument and the cited base-change assertion apply to the two factors of the composite diagonal. I explicitly use quasi-separatedness of both f and g here, rather than falsely deriving it from local finite presentation. This step is elementary relative to its stated definitions and citations.

Step 4 uses lem-sfb-scheme-etale-source-target-properties only for its explicit assertion that local finite presentation is etale local on source and target. It uses lem-sfb-space-etale-presentation-property-criterion for both existence of a presentation with surjective source and the any-presentation direction; I read those sentences in the node. It uses the fibre-product node to construct X_V, and def-trf-algebraic-space to choose its scheme atlas and to interpret etale/surjective maps on all scheme tests. The only additional permanence assertion is the composite of two surjective etale SCHEME maps; this is stated verbatim by lem-weil-pbc-etale-covering-composition. I did not assume an algebraic-space composition theorem in constructing d: every scheme test is explicitly factored into two scheme covers. Both f and g can remain nonrepresentable.

Step 5 uses exactly the scheme local-finite-presentation conclusion of lem-sbc-locally-finite-presentation-composition on h and k from step 4. The two presentation nodes justify passing from kh back to gf because d is surjective etale and c is etale; c need not be surjective, as the criterion explicitly allows. Thus no simultaneous-atlas lemma is hidden. The step verifies the actual identity (gf)d=c(kh).

Step 6 assembles three properties already proved and the inline definition of finite presentation; it uses no external lemma and has no citation entry. Each step is shorter than 2000 characters, and none hides a separate comparison or standard omitted argument.

I checked small cases: empty source/empty base and empty atlases give vacuous local-finite-presentation and closed-immersion tests; identity maps give identity diagonals and chart composites; for two scheme closed immersions the scheme-test construction reduces to the given composition lemma; on affine scheme charts the h,k composite is the usual composition of finitely presented algebra maps. Arbitrary base-change maps are allowed in the diagonal test, and no quasi-compactness, Noetherian or separation hypothesis is imposed on the base. I also checked finite presentation retains its quasi-separatedness clause. All cited statements were opened and their quotations in citations.json are exact full statements, so the reviewer can assess the scope used in each application. The B--E checklist revealed no need for a new node, no source-statement dispute, no circular edge, and no unresolved mathematical gap.

## Unfinished work

None in the stage-1 split. Awaiting the required dry run and direct delivery.
