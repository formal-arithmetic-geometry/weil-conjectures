# Stage-1 report: lem-weil-pbc-ringed-slice-evaluation-transpose

## Files written

- dag/nodes/sec-six-functors/lem-weil-pbc-ringed-slice-evaluation-transpose.json: existing statement, split into five steps. Mathlib verdict: no exact or one-line-specialization match.
- citations.json: one verbatim statement quotation for each citation of each proof step.
- searches.jsonl: actual additional Mathlib searches, retaining all inherited searches in the item.
- report.md: this report.

No new nodes and no new Mathlib leaves. The other retained root-level JSON and item.tmp are interrupted-attempt artifacts; the delivery item is the file under dag/nodes/.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures source for the exact blueprint tag/id and slice/evaluation terminology, and inspected the available categorical internal-Hom infrastructure. No project declaration gives the three equations for arbitrary unbounded objects on a small ringed site. Generic complex adjunctions and underived module evaluation do not attach this item. Upstream master is reference material, not an attachment source.

## WANTED

None. The local Stacks sources and the current parent blueprint proof supply the constructions needed here.

## Corrections and retained work

The earlier sandbox contained an item split and citations, but no report and no active delivery process for this item. I retained its statement, historical Mathlib searches, citations' underlying sources and blueprint ancestry. I compared it against the shared item: the mathematical statement agrees. The only statement edit adds the definition-node reference specifying the existing canonical representative normalization of the counit; it adds no hypothesis or new choice of adjunction.

The earlier proof spoke of computing arbitrary derived arrows by homogeneous chain maps, and used the Hom complex in a tensor without explicitly accounting for its possible failure to be K-flat. I repaired both: introduce a flat-term K-flat replacement Q of the Hom complex before evaluating, and derive the transpose identity formally from evaluation and naturality in the derived category. I removed the vague grading-sign qualification in the transpose formula; evaluation in the order Hom(P,I) tensor P is unsigned, and the Koszul sign appears in the symmetry equation. No imported statement dispute or counterexample to the item was found.

The source proof is an agent blueprint paragraph. The item's proof_origin remains agent: Stacks 08JB and 07A4 give the comparisons, but I am not claiming that a Stacks tag states the simultaneous three coherence equations verbatim.

## Review by Q78

I read coord/brief-stage1.md, delivery-errors B through E, the stage document, the three levels in SETUP.md, the unit/chapter records, GOAL.md and dag-sync.md. The unit is general biduality and this item supplies the slice computation in the final paragraph of lem-weil-delta-restriction.proof.md in main-20261015. I read that paragraph: restriction of evaluation and transposition are its route. I keep that route; no SGA source is used.

For the item I read sites-cohomology.tex, section-internal-hom (08J7), lemma-internal-hom (08J9), lemma-restriction-RHom-to-U (08JB), lemma-restrict-K-injective-to-open (08FI), lemma-pullback-K-flat (0G7E), lemma-K-flat-resolution (06YS), and lemma-pullback-tensor-product (07A4), including the latter's description by ordinary tensor pullback on total-complex summands. I also read section-hom-complexes (0A8X) and lemma-compose, and sites-modules.tex definition-localize-ringed-site (04IX) and lemma-tensor-product-pullback. These distinguish an actual slice localization from an arbitrary morphism or a closed immersion. There are no new nodes whose sources need separate review.

Step 1: I opened all seven cited statements. lem-pc-kflat-resolution explicitly gives flat-term K-flat resolutions for every complex, so it supplies P and Q, without boundedness. prop-pur-kinjective-resolutions-exist explicitly covers small sites and arbitrary complexes, supplying I. def-pur-derived-internal-hom identifies Hom(P,I) with RHom and includes independence of K-injective representative. lem-pur-kinjective-restrict-localized gives exactly the K-injectivity of rI. The K-flat preservation clause in lem-weil-pbc-ringed-topoi-derived-tensor-pullback applies to the identity coefficient map of the localization, giving flat-term K-flat rP,rQ. def-weil-pbc-ringed-derived-restriction specifies the functor induced by exact module restriction. lem-weil-pbc-site-derived-tensor-descent supplies the natural canonical tensor model on the pair Q,P. Smallness is inherited by C/U in the same module universe. I do not infer flatness or boundedness of I or of the Hom complex.

Step 2: I opened the five cited statements. def-pur-localized-ringed-site explicitly includes relocalization C/V = (C/U)/(V/U), with sectionwise identity, and def-pur-hom-complex gives local families, sectionwise products and their signed differential. Thus no interchange of a non-exact inverse image with an infinite product is being assumed. lem-weil-pbc-ringed-internal-hom-exact-restriction states the unbounded slice comparison, with successive restrictions. The canonical tensor comparison and its naturality are in lem-weil-pbc-ringed-topoi-derived-tensor-pullback; def-pc-tensor-complex-sheaves specifies the total differential and summands. The explicit local identification fixes which comparison is used, instead of taking an arbitrary isomorphism of objects.

Step 3: I opened all six cited statements. def-coef-ringed-tensor-hom-model specifies the actual canonical adjunction and its representative uncurrying on pure tensors for K-flat source complexes; its formula is precisely q(x)(p). This is a definition of the canonical normalization already present in the item, not a claimed existence theorem derived from a definition. def-pur-derived-internal-hom explicitly permits the canonical change of K-injective representative, so I can compute with I and rI. The Hom and total-tensor definitions give the displayed differential calculation. def-pur-sheaf-tensor-product is sheafification of the presheaf tensor, so equality of bilinear local-generator maps determines the sheaf morphism; applying this to each summand determines the total-complex map. lem-weil-pbc-site-derived-tensor-descent identifies the image of Q tensor P with the derived source. I added Q because A need not be K-flat. This step proves the evaluation equation rather than citing another node for that clause.

Step 4: I checked the three cited statements again. The closed adjunction/counit meaning is in def-coef-ringed-tensor-hom-model, naturality of rho in both derived arrows is explicitly in lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and restriction is a functor by def-weil-pbc-ringed-derived-restriction. The written three-line calculation untransposes the proposed arrow to the required restricted f. Injectivity of a bijection then proves the transpose identity. This is elementary categorical algebra once the previously established evaluation equation is available; it does not invoke the chain-map representative of an arbitrary f.

Step 5: I opened its six cited statements. The same K-flat existence, preservation and tensor-model statements apply to the pair P,R. The localized-site and tensor definitions give the local generator formula and total differential. The symmetry equation is then the explicit Koszul sign calculation on p tensor z. This is an elementary calculation, not a new theorem about a different choice of symmetric monoidal structure.

I checked every citation against the actual cited node's statement and wrote verbatim quotes into citations.json. All non-elementary inputs are existing nodes; the two elementary steps are written calculations. Off-unit resolution and ringed-site theorems are declared in split_report.tool_uses: they are generic tools, not replacements for the biduality unit's route. I did not set maintainer-owned tool_uses.

Small-case checks: if U is terminal and restriction is identity, all three equations reduce to the identity comparisons. With L=0 or M=0 the equations are zero-map identities. With ordinary modules in degree zero evaluation is h tensor p mapped to h(p) and symmetry has sign +1. Odd-degree inputs give the required minus sign on each side of symmetry. Unbounded inputs use products in Hom and direct sums in tensor without any boundedness truncation. No perfectness, finite generation, invertibility of evaluation, or equality of different coefficient categories is used.

Against B: there are no new statement-only nodes or duplicate leaves to audit, the item introduces its own data, sources are tagged and labelled, and inherited source metadata is retained. Against C: all cited statements were opened as above, definitions are used for their actual formulas, and no uncited substantive theorem is hidden in a 'transport' instruction. Against D: the main equations are proved here and not moved to clause-sized new nodes. Against E: I verified smallness, the identity coefficient ring map, exactness of restriction and the unbounded scope at every application. Each proof step has fewer than 2000 characters; none contains an unexposed lemma. No Lean, compiler, Lake, live repository mutation or git command was run.

## Not duplicates

No new nodes.

## What could not be finished

Nothing mathematical remains in this split. Server dry-run and delivery results are recorded below when available.
