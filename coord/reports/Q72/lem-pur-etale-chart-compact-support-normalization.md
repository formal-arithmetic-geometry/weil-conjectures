## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-chart-compact-support-normalization.json`: existing statement split into eight proof steps; no Mathlib match for the full assertion; statement unchanged.
- `citations.json`: verbatim supporting statement excerpts for all 37 proof citations.
- `searches.jsonl`: five searches actually performed with msearch.py; the original item's five historical search records are preserved in its JSON.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and compact-support/closed-chart normalization terminology. No declaration there supplies all of the coefficient, geometric, ordinary unbounded adjunction and normalized composition clauses. The deformation chart theorem is about section invariants, not this statement.

## WANTED

None for this split. The coefficient prerequisites already have nodes; their reports record the historical missing Local Fields reference. This proof uses their statements, not an unconsulted source.

## Corrections and findings

No statement correction or route change. The item is a new-target-chain node: `blueprint_refs.py ancestor` returns null, consistently with its existing blueprint.from.node. Retained its complete via chain and the explicit Locality and Charts supplement place. The current main-20261015 `sk-lem-sp-reduction-exceptional.proof.md` discusses locality and charts; the arbitrary-map closed chart is a prerequisite extracted by the existing parent, not a literal theorem in that paragraph. Thus proof_origin.by is agent. Read also the current purity-transport unit and its recorded chapter; neither is changed.

The pointer to lem-exc-closed-support-triangle is not used to infer exactness of closed direct image: its statement describes a triangle and termwise direct image, rather than asserting that exactness. Step 6 instead applies lem-sfb-quasifinite-compact-support-exact and the proper clause of lem-cbc-proper-support-sheaf-composition. This fixes the potential C4 gap without changing the statement's original pointer or creating a duplicate node. No SGA source is used.

## Not duplicates

No new nodes. Before deciding none were needed, searched all dag/nodes by Noetherian/open/finite-type/separated/compactification terms and by tags 01OW, 01OX, 01T6, 0F7B and 0F7J. Searched the entire imported blueprint with blueprint_refs.py for compact support and closed chart. Reused the existing general nodes rather than making closed-chart geometry, open adjunction or closed pushforward copies. None of the blueprint search results states this entire normalized closed-chart assertion.

## Tool uses

The cross-unit quasi-finite compact-support theorem supplies the exact support functor and its unbounded refinement-invariant comparison, as the item explicitly requires. The support-composition theorem supplies only its proper specialization. The coefficient DVR and finite-quotient results, finite-type cancellation/composition, Noetherian open/affine criteria, affine separatedness and Nagata are generic tools for verifying domain hypotheses. Open sheaf adjunction/exactness and localization tools provide the prescribed ordinary unbounded open adjunction. All off-unit statement uses are declared in split_report.tool_uses; this preserves the chosen compact-support route and does not replace any purity argument.

## Review by Q72

I read the full item, its statement dependencies that enter the proof, and every cited node statement. I compared the intended compositor with Stacks more-etale.tex Tags 0F7B (lemma-shriek-proper-and-open, torsion-ring case on arbitrary unbounded inputs), 0F7J (lemma-shriek-composition and its proper/open tower), and 0F51 (lemma-proper-f-shriek). I read properties.tex 01OW/01OX, morphisms.tex 01T6, 01QR and 01W5, schemes.tex 01KU/01KV, and sites-modules.tex 03DI/03DJ/04JC with etale-cohomology.tex 03S5. The two unbounded normalization nodes and the quasi-finite support theorem are the precise DAG interfaces used; no bounded-below theorem is silently promoted.

Step 1 uses the DVR statement's finite residue field, maximal ideal and extended absolute value, and the finite-quotient statement's clause 2. The l-adic-number definition gives the normalization at ell. I checked ell lies in the maximal ideal, so ell=ta and ell^n belongs to (t^n); an equality of ramification index with n is neither assumed nor needed. Characteristic p different from ell gives its inverse in k.

Step 2 applies finite-type-over-Noetherian to X and Y, and the open-subscheme lemma to U and V. To prove quasi-compactness of the immersions (rather than just compactness of their sources), it applies the same open-subscheme lemma on each affine open of the target, using pqf-lem-affine-open-locnoeth for its Noetherian coordinate ring. The finite-type-open and composition statements then give the structure morphisms. Each cited statement says precisely this; scheme conventions alone would not have sufficed.

Step 3 uses the actual affine-space chart R[x_1,...,x_r], its finite list of generators, the finite-type composition statement, and the Noetherian theorem. The complement W is treated as an arbitrary open, with exactly the affine-preimage argument of Step 2; it is not presumed affine. This avoids an incorrect affine-intersection or principal-open assumption.

Step 4 uses affine-source separatedness for U,V,P, separated cancellation for W and then for every k-morphism in the diagram, finite-type cancellation clause (b) with separated structure maps, qcqs-over-affine for the targets, and Nagata for compactifications. I opened the finite-type cancellation statement and checked that its clause (b), not only its locally-finite-type clause, is available. All targets are schemes already proved finite type over k; all cancellation maps are k-morphisms. No abstract composite-separatedness fact is left uncited: separatedness of each composite follows directly from its source structure map by the cited cancellation theorem.

Step 5 uses the exactness, evaluation-counit and exact constant-coefficient inverse-image clauses of the three sheaf statements. The termwise-adjunction theorem supplies the homotopy adjunction. Localization's natural-transformation descent and faithfulness supply the descended unit/counit and their triangle identities. These are a short assembly of the cited general statements, not a new derived-adjunction lemma. The ordinary constant-ring module categories agree throughout, including the inverse-image statement's identification of the pulled-back constant ring.

Step 6 checks every hypothesis of the quasi-finite theorem: A is finite commutative, U and P are Noetherian, i is separated finite type, and its fibres are closed subschemes of residue-field points by closed-immersion base change. The definition of quasi-finite therefore applies. Closed-immersion properness and the proper clause of the support-composition statement give i_!^supp=i_*. Hence exactness and the comparison both come from cited statements, with the stipulated canonical support normalization. I specifically corrected the potential unsupported inference from the triangle node described above.

Step 7 uses the compact-support definition on the identity-proper compactifications for the opens, the refinement comparisons of the unbounded theorem, and the explicit source-open-composition statement. Identity pushforward is exact already on complexes, so R(id)_*=id requires no cohomological bound. The open-source theorem explicitly specifies the ordinary evaluation-adjunction normalization used in Step 5.

Step 8 writes the arrows and directions: alpha_(f,u), equality fu=v*pi*i, inverse alpha_(v,pi*i), and Rv_! applied to inverse alpha_(pi,i), followed by the open/closed identifications. Each factor is natural and invertible by the cited statements; their refinement and associativity clauses prove independence. This is the prescribed left compositor, with no assertion about an exceptional right adjoint and no use of smooth purity. The non-elementary steps are all under 800 characters and contain no hidden comparison lemma requiring a new node.

Small cases checked: r=0; U empty; W empty when i is the identity; nonreduced affine charts; n=1; ramified E; and arbitrary unbounded complexes. The geometric arguments allow empty schemes and never require reducedness, affine complements, algebraically closed k, or smoothness of f. The ring argument works for all ramification indices. On identity charts the specified identity/composition normalizations give the identity under the ordinary unitors. The entire argument stays on ordinary small-etale constant-A module categories, never interchanging them with adic or pro-etale categories.

The five new Mathlib searches were read as returned. LeanFinder first returned normalization schemes and affine-chart algebra facts, then with a different phrasing returned the structure-sheaf module pseudofunctor; neither is an etale compact-support theorem. Loogle returned abstract adjunctions; LeanSearch returned topological function supports and structure-sheaf restriction; grep found no matching compact-support compositor declaration. No Mathlib leaf is claimed from these partial matches. Every B–E issue was considered: no statement-only children or restated clauses were introduced, no tags substitute for DAG citations, and all citation quotes are copied verbatim from the nodes actually used.

## Unfinished work

None in the stage-1 split. Existing prerequisite nodes remain separately owned stage-1/Lean work. Server review_split passed with zero new nodes; the required delivery dry run follows this report.
