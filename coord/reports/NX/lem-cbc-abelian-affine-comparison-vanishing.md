## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-abelian-affine-comparison-vanishing.json: statement retained; nine-step split of Stacks 099U. No Mathlib match.
- citations.json: verbatim cited statements for every step citation.
- No new nodes; no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures for the exact blueprint id and affine vanishing, and inspected SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean:107-110. The related declaration AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective has sorry and a different conclusion (comparison direct-image acyclicity), so cannot close this item. The reference master is not used as finished-proof evidence.

## Wanted sources

None. All proof sources are present locally.

## Corrections and scope

The item statement agrees exactly with Stacks proetale.tex, Tag 099U, lemma-affine-vanishing: affine base, injectivity in abelian sheaves on the small etale site, all positive degrees. It needs neither a torsion nor a finite-ring hypothesis. No statement dispute. The unit sk-prop-sf-comparison and chapter sec-smooth-purity were read; this node supplies the affine comparison input below the unit's existing comparison route, not the unit's key statement. No unit realization fields are changed.

The proof must not infer that etale inverse image to an arbitrary ind-etale U preserves injectivity. The split instead descends the covering to objects of the ORIGINAL etale site of Y, where the original J is injective. Likewise, the set-valued section formula is promoted explicitly to an additive formula by naturality for the group operations, without identifying finite-module sheaves with arbitrary abelian sheaves. In self-review I replaced an imprecise use of ind-etale stability for etale composition by the actual etale composition, finite-limit, and cover-preservation nodes. Source references for ind-etale base change and composition are 097J and 097K.

## Mathlib and duplicate searches

Repeated searches using msearch.py are recorded as run in searches.jsonl and the item's mathlib_searches. Two semantic phrasings returned cotangent cohomology or K-injective complex facts, not comparison acyclicity. Loogle with ProEt and Injective returned no hits. Grep returned no vanishing match; a second grep in AlgebraicGeometry/Sites returned Proetale.lean and ElladicCohomology.lean. I read those files: topology and ell-adic sheaf/cohomology definitions supply no such theorem. LeanSearch returned Internal Server Error, recorded unavailable.

Searched the entire DAG by tags, labels and concepts, and blueprint_refs.py by affine vanishing, 099S, 099T, 0GLZ and ind-etale. The zero blueprint matches for the three comparison tags do not mean no existing created node: lem-cbc-comparison-pullback-sections supplies 0GLZ/099T, while 099S follows from the existing arbitrary-abelian 09YQ node and that section formula. All other inputs were found already in the DAG. Thus no duplicate or clause-restatement nodes were created. Reachability checks found no dependency path from any selected theorem back to this item.

## Not duplicates

No new nodes.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their owners' items. No Lean was written or compiled, and no delivery was pushed.

## Review by NX

I read Tag 099U (lemma-affine-vanishing) and its whole proof at proetale.tex:3866-3950, the section formula and limit formula preceding it (0GLZ, 099T, 099S), Tag 03F9 (lemma-cech-vanish-collection) at sites-cohomology.tex:1565 and Tag 03AW (lemma-injective-trivial-cech) at 1334, the ind-etale definition and permanence statements at proetale.tex:1159-1187, the weakly-etale structure statement at 1585 and affine cover refinement at 2216, and Tag 0EYL (lemma-colimit-affine-sites) and its qcqs proof at etale-cohomology.tex:7336-7370. These are the exact inputs to 099U, not a finite coefficient replacement.

Step 1 reads the full statement of lem-cbc-comparison-pullback-sections: it gives both the value formula and naturality for arrows, plus the etale-object unit identification. def-weil-pbc-site-comparison-morphism explicitly says its left adjoint preserves finite limits; addition, inverse and zero are therefore preserved in the formula. Step 2 uses the affine special case, explicitly for arbitrary abelian G, of lem-weil-pbc-etale-cohomology-limit-of-schemes in degree zero. Its pullback maps and the section formula's arrow description give the same restriction maps. Affine stages and intersections are qcqs, so no Noetherian assumption is smuggled in.

Step 3 uses precisely the exactness conclusion of lem-weil-pbc-filtered-colimit-abelian-groups-exact; the finite-product comparison is proved by the finite direct-sum universal property. Its two exact sequences identify kernels, images and cohomology, rather than citing an unrecorded homology-colimit assertion. def-weil-pbc-site-cech-complex gives the product formula and alternating restriction differential verbatim. The argument is elementary relative to those statements. Step 6 invokes only these already established steps and is marked elementary.

Step 4 uses lem-weil-pbc-ind-etale-basis for finite refinement and closure under intersections, and lem-weil-pbc-ind-etale-stability for the stronger requirement that maps between basis objects are ind-etale. This last requirement is not supplied merely by membership in the basis. Its statement explicitly covers every algebra map between two ind-etale algebras. The general-site criterion is the node that allows pro-etale sites, whereas the etale-only variant would not apply.

Step 5 uses the ind-etale definition for the affine etale inverse-limit presentation, the directed-cofinal theorem for a directed indexing set without a size gap, the affine-limit existence theorem, and lem-kun-fibre-product-limits for every repeated intersection. The finite product of directed sets and its projections are handled explicitly; a point of a limit cover member maps to a point at every stage, establishing joint surjectivity of every stage cover. No converse lifting assertion is made. For n=0 the base is empty and the Cech terms are zero, so no nonempty-cover hypothesis was added.

Step 7 reads clauses (3) and (4) of lem-weil-pbc-affine-etale-site-colimit: the actual finite cover descends, not merely its individual schemes; the identity target is recovered by descending its isomorphism and inverse. Every U_b is affine, verifying that node's qcqs hypotheses. The separate etale composition/cancellation node, finite-limit base-change node and continuous base-change node explicitly give the etale composite objects, intersections and preservation of the covering family at every later stage. I corrected this step during self-review because ind-etale composition alone does not assert etale composition.

Step 8 checks the full statement of lem-weil-pbc-injective-sheaf-cech-acyclic: it applies to coverings of ANY etale object of Y and to an injective in Ab(Y_et), exactly the hypothesis retained here. The section formula identifies all face maps, so an isomorphism of groups degree by degree really is an isomorphism of complexes. Step 9 uses all three numbered hypotheses of lem-weil-pbc-site-cech-vanishing-criterion, already verified, and the two ind-etale definitions to put Y itself in the basis. The empty affine scheme, identity cover, zero sheaf, repeated cover indices and positive degree p=1 were checked: the same products, signs and tail-colimit arguments apply. There are no new statements to test independently, and no proof of a cited node is used in place of its statement.

Cross-unit generic tools are declared in split_report.tool_uses; they realize the exact Cech/limit proof of 099U and do not replace any step of the unit route. Every quote in citations.json is copied from the opened cited node statement. B1-B9 are satisfied with no new nodes; B10's closed attachment check fails for the relevant sorry declaration. C1-C4 were checked as described above, C5 by whole-DAG/blueprint searches, C6 by dependency reachability, and C7-C8 by the declared tools. D1-D5 are addressed by carrying the two limit reductions in this item's own steps. For E1-E7 I checked affine/qcqs and small directed hypotheses, the distinction between a sheaf of sets and an abelian sheaf, actual fibre products over U, and compatibility of every omitted-factor projection with the section comparison. No source error or weakened conclusion was found.

The first dry run rejected the phrase “the item’s hypothesis” in step 8 as B2. I replaced it with the explicit assumption that J is an injective abelian sheaf on Y_et; no mathematics or dependencies changed.

## Second reading by NX

Item statement: read proetale.tex Tag 099U, label lemma-affine-vanishing, against every hypothesis and conclusion; affine Y, arbitrary injective abelian J and q>0 agree exactly. Zero sheaf, a field, empty scheme and q=1 introduce no exception; degree zero is intentionally excluded.

Step 1: opened lem-cbc-comparison-pullback-sections and def-weil-pbc-site-comparison-morphism against 0GLZ/099T (lemma-describe-pullback-from-etale, lemma-fully-faithful); naturality in the sheaf and finite-product preservation give all abelian operations and naturality in the object gives restrictions; accepted.
Step 2: opened lem-weil-pbc-etale-cohomology-limit-of-schemes and the section formula against 099S (lemma-limit-pullback); its explicit affine arbitrary-abelian specialization in degree zero has exactly these compatible maps and no torsion restriction; accepted, including affine/qcqs transitions.
Step 3: opened filtered-colimit exactness and the full general-site Cech definition against 00DB and 099U's first displayed Cech equality; finite sums give finite-product comparison. Repaired the kernel/image justification by factoring each differential through its image and preserving the epi/mono factors. Empty product is zero; no infinite-product commutation is claimed.
Step 4: opened the ind-etale basis definition, basis theorem, stability theorem and general-site criterion against proetale.tex lemma-proetale-affine, proposition-weakly-etale and lemma-ind-etale-permanence, and sites-cohomology.tex 03F9 (lemma-cech-vanish-collection); finite refinements, ind-etaleness of basis arrows and all repeated intersections verify (1),(2); accepted.
Step 5: opened the ind-etale definition, directed-cofinal theorem, fibre-product-limit theorem, affine-limit theorem, stability theorem and Cech definition against 099U second paragraph and 097J/097K (lemma-base-change-ind-etale, lemma-composition-ind-etale); hypotheses hold for affine systems. Expanded change of index into an explicit correspondence of cones, also for repeated indices. Stage covers are surjective by projecting actual limit preimages; n=0 forces empty U and a zero complex.
Step 6: checked against the conclusions actually established in steps 2,3,5 and the first Cech equality of 099U; direct substitution gives the reduction to finite affine etale covers, so elementary=true is justified; accepted.
Step 7: opened every cited statement, especially clauses (3),(4) of lem-weil-pbc-affine-etale-site-colimit against 0EYL (lemma-colimit-affine-sites), qcqs proof, and 099U third paragraph; all U_b are affine. Expanded descent of the target isomorphism, inverse and identity equations, and composition of cover arrows with it. Etale composition, base change and cover preservation supply the later stage covers and intersections; accepted.
Step 8: opened the comparison section formula and injective-sheaf Cech theorem against 099T and sites-cohomology.tex 03AW (lemma-injective-trivial-cech); J remains injective on the original Y_et, and stage covers cover objects of that site. Replaced the abbreviated repeated computation with componentwise section comparisons and each alternating differential term, then step 3's cohomology calculation; accepted, including p=1 and repeated cover indices.
Step 9: opened the general-site criterion and both ind-etale definitions against 03F9 and the final sentence of 099U; steps 4--8 meet all three conditions and Y belongs to the basis via the constant identity presentation; accepted also for the empty scheme and identity cover.
New nodes: none; the sandbox contains exactly the item. B1--B7 create no outstanding statement-only, definition, source or Mathlib-leaf obligations.

Changes: expanded four elementary justifications in steps 3,5,7,8 (kernel/image colimits, coordinate reindexing, target descent, second Cech comparison) to remove implicit arguments under C3/E5. No statements, dependencies or source claims changed; all 30 citations were checked as full verbatim statements of the opened nodes, with exactly the step citation coverage. No new node or Mathlib leaf was added. The first worker's review is retained.

Independent search: msearch.py grep 'Proetale.*[Aa]cyclic|[Aa]cyclic.*Proetale|[Aa]ffine.*[Ii]njective' ran and returned 25 hits, all affine-space function injectivity, not this topos theorem; actual output is appended in searches.jsonl. DAG search for 099U and the label found the existing finite-coefficient module comparison lemma, whose fixed finite-ring hypotheses do not imply this arbitrary-abelian statement. Read the related slopmaster2 LowerStarAcyclic.lean declaration: it ends in sorry and asserts direct-image acyclicity, so supplies no finished attachment. No Lean or compiler was run, and no live project file was edited directly. Generic cross-unit tools remain proposals in split_report.tool_uses for the maintainer to accept, not maintainer-owned tool_uses fields.
