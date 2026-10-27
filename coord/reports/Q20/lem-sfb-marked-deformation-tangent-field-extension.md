# Stage-1 report: lem-sfb-marked-deformation-tangent-field-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-marked-deformation-tangent-field-extension.json: statement, split; no Mathlib match. Six proof steps, no statement change.
- citations.json: one verbatim statement excerpt for each cited node in each step.
- report.md: this report. searches.jsonl is the search command's unmodified log.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, predeformation/Predeformation, Schlessinger, marked deformations and deformation tangent concepts found no declaration stating the item. No compiler or Lake command was run, and no Lean file was written.

## WANTED

None. All the needed Stacks sources are present.

## Findings and corrections

The statement is retained. The empty proof has been replaced by the arguments of Stacks artin.tex Tags 07WU (lemma-deformation-category) and 07WX (lemma-change-of-field), and formal-defos.tex Tag 07WB (lemma-tangent-space-change-of-field). Rather than introduce a new lemma for each clause of the item, the proof actually constructs the marking, the equivalence on marked fibres, and the tangent comparison. Existing DAG statements provide the non-elementary Artinian algebra and the scheme pushout.

I read the chapter and unit records, SETUP.md's three levels, GOAL.md, the worker brief and delivery-errors B–E (including the merged copy). I read the current blueprint under literature/blueprint/latest: sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md, its proof and its direct-images proof. Its direct-image clause (3) is the source of the existing deformation/moduli prerequisite chain; this item makes no change of that route or to any target. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints that same null ancestor, rather than an id. I have retained the precise inherited place and via list, and documented the finding in split_report.blueprint. No new node needs an ancestor. Whole-blueprint searches for deformation, tangent space, marked deformation, 07WU, 07WX and 07WB found no equivalent statement; same_as remains [].

No obsolete statement dependency was removed. proof_deps is the union of the steps' uses. The Artinian-local nilpotence citation is an existing Mathlib leaf outside the unit, so it is an allowed tool; all other cited statements follow the item's unit. No unsolicited top-level tool_uses field was added.

## Mathlib searches

Ran the prescribed msearch.py command for this item with LeanFinder (two different phrasings), Loogle, LeanSearch and grep. All five calls succeeded and their actual query strings and returned names are recorded from searches.jsonl. The results concern cotangent modules of ring extensions, formally smooth algebras, manifold tangent spaces, and elementary tensor-product linear algebra. None concerns marked deformation groupoids or states the item under its hypotheses. The earlier imported searches remain present, and the fresh logged searches are appended. No new node is proposed, so there is no new-node duplicate-tag list to supply.

## Not duplicates

No new nodes. Reused lem-sfb-artinian-finite-residue-restriction (07W8), lem-sfb-artinian-finite-type-residue-criterion (02HV/07DT), lem-sfb-artin-local-test-algebra (06GH), lem-sfb-affine-closed-pinching-pushout (0ET0), lem-sfb-artin-rs-tangent-tensor (06IH), and the existing Artinian nilpotence Mathlib leaf.

## Review by Q20

I checked the source proofs with the node statements open. artin.tex's marked category equation and predeformation lemma show exactly why a marked fibre at k has a unique arrow between any two objects, even if y has automorphisms. This is step 1, using the explicit pseudofunctor and predeformation definition in def-sfb-artin-deformation-test-category. The direction of the marking is eta|k to y, and the unique arrow is alpha' inverse composed with alpha.

For step 2, I checked 07WU's four-ring diagram and read formal-defos.tex lemma-fiber-product-CLambda. lem-sfb-artin-local-test-algebra states both that P is Artinian local with residue k and that maximal ideals are nilpotent. Thus the surjection A2 to A has nilpotent kernel. The statement of lem-sfb-artinian-finite-type-residue-criterion, checked against morphisms.tex Tag 02HV, upgrades all four rings to finite type over R. Finally lem-sfb-affine-closed-pinching-pushout, checked against more-morphisms.tex lemma-basic-example-pushout (0ET0), gives the pushout for arbitrary A1 to A and surjective A2 to A. I do not try to deduce the affine formula from the weaker statement of the global pushout node.

Step 3 uses the equivalence already obtained in step 2 and the definition of marked arrows. Its construction writes both essential surjectivity and full faithfulness: the two markings agree over k because the input arrow over A respects them. It does not invoke an uncited groupoid descent theorem. The finite-type assertion for l is checked by adjoining a finite k-basis to R-algebra generators of k, so no separability or algebraic-stack hypothesis enters. The same diagram then proves (RS) over l.

For step 4, I read every clause of lem-sfb-artin-rs-tangent-tensor, especially naturality for every k-linear V to W; its statement is enough to obtain the zero, scalar and sum operations through the explicit square-zero maps. The sum and projection squares after extending k to l prove that rho respects addition as well as k-scalars. I checked the square-zero product here is k plus (k direct sum k), rather than the tensor product of dual-number algebras (which would leave an unwanted epsilon1 epsilon2 term).

For step 5, I read formal-defos.tex situation-change-of-fields (07W8) and artin.tex 07WX in full. The statement of lem-sfb-artinian-finite-residue-restriction guarantees C=B times_l k is a test ring; it is not used for any deformation assertion. Nilpotence is separately obtained from lem-weil-pbc-artinian-local-noetherian-nilpotent, whose statement I read. The finite-type criterion and the affine pushout node supply exactly the remaining hypotheses needed for the assumed equivalence on Y. The marked-fibre equivalence is written out with gamma inverse followed by alpha over l, and its inverse uses the triple (y,eta,beta inverse). This handles arrows as well as objects, and naturality uses the actual inclusions C to B. No general change-of-field lemma restating the item was introduced.

For step 6, I read formal-defos.tex 07WB's proof and used the exact naturality clause of the existing tangent-tensor node, rather than using its proof. The coordinate formula l[V] times_l k = k[V_k] is explicit. The projections and sum maps show additivity of the resulting bijection; multiplication by any a in l is a k-linear map on V_k and corresponds to 1 tensor m_a, proving l-linearity. The two ring inclusions give the actual rho on v tensor 1 and hence the requested formula on v tensor a. Every use of finite-dimensionality is only for l or V_k; no basis of T_y is chosen. This also checks the infinite-dimensional tangent-space case.

I tested l=k (the comparison reduces to the identity), B=l (C=k and the marked groupoids are contractible), V=0 (only the zero class), and a=0,1. The construction uses neither separability nor division by [l:k], so purely inseparable finite extensions remain covered. Every step is shorter than 2000 characters. The non-elementary steps cite existing statements; the elementary steps are the explicit coherence and marked-fibre arguments from the definitions. Every citation quote is programmatically checked as a verbatim substring of the cited statement. This is my own review and signature; the maintainer still supplies the independent review.

## Unfinished work

None in the mathematical split. The first server dry run passed and saved its durable .stage1-ready.json receipt. After extending the citation excerpt for the test-algebra input to include its fibre-product assertion, the final dry run and push are performed with the prescribed delivery command.
