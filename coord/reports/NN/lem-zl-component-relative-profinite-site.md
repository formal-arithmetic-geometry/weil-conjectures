## Worker report

Item: lem-zl-component-relative-profinite-site. Group NN. Stage 1 only. Date 2026-10-18.

### Files written

- dag/nodes/sec-zeta-weil/lem-zl-component-relative-profinite-site.json: statement node, now split; statement unchanged; no exact Mathlib match.
- citations.json: 17 entries, one for each node used in each numbered proof step, with literal statement quotations.
- report.md: this report and the direct-delivery self-review.

No new DAG nodes and no Mathlib leaves. research/ contains PDF text extracts and the sandbox writing script; searches.jsonl contains the actual search-command log. These are working material, not additional DAG deliverables.

### Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the exact blueprint tag/id and for component/profinite terminology; read RingTheory/ProEtale/PullbackProfinite.lean and the component-pullback section of WContractible.lean. The latter constructs a related ring and topological fiber homeomorphism; it does not state all of the relative site functor, its preservation assertions, and the factorization of geometric morphisms. The full item is not an attachment. Master Basic.lean was read only as reference material for the absolute test-object convention, never as evidence of closed proofs.

### Wanted literature

None. Both cited papers and the relevant Stacks source are present locally.

### Audit findings and changes

The seeded item had no proof. Its statement agrees with the Hemo–Richarz–Scholbach paragraph before and after (4.1), with finite coproduct preservation made explicit. It needs no mathematical correction and no STATEMENT-DISPUTED marker. The construction only assumes T affine, as in the more precise statement after Bhatt–Scholze Lemma 2.2.8; the w-contractibility hypothesis belongs to the subsequent derived equivalence, not this site construction.

The key reuse is lem-zl-affine-component-site-projection, an existing node from a different split in the same unit. Its statement supplies the affine ind-etale locally ringed pullback, finite limits, covers, and geometric morphism. Creating another node for any of those assertions would duplicate it. The item still needs the specified finite-clopen presentation, its independence, finite coproducts, and the absolute-point factorization; the steps prove those rather than moving them to new nodes.

The old blueprint.from.place was a description of the pre-update coefficient route. It now locates this subordinate site construction in the relative-duality/finite-projective identification of the current ancestor, retaining the full created.item ancestry and via list. The item is not the unit's key node, so no unit record was changed. The current main-20261015 proof and chapter/unit records were read. There is no departure from the unit route.

The paper's shorthand that finite stages are objects of the Zariski site is read in its disjoint-union sense. For a two-element fiber the stage consists of two copies of a clopen subscheme, not one open immersion. The item's explicit disjoint-union wording already handles this correctly.

### Searches and reuse

Read the whole imported DAG/blueprint matches for profinite, component/connected-component and finite-quotient terminology, including tools/blueprint_refs.py searches and its ancestor result. The relevant existing nodes are lem-zl-affine-component-site-projection, lem-sfb-finite-quotient-fiber-product, lem-weil-pbc-profinite-test-object-functor and the general slice-projection statement lem-trf-slice-subtopos-site-presentation. The w-local-only component-ring-pullback node was not used: its extra w-local hypothesis is absent here.

Preserved the item's original recorded Mathlib searches, read their returned declarations, and appended only the additional searches actually run through msearch.py in this session. LeanFinder was run with two phrasings; Loogle with AlgebraicGeometry.Scheme, ConnectedComponents; grep for component/pro-etale combinations; and LeanSearch for the relative geometric morphism. Returned absolute profinite presentations, affine-limit results, ordinary etale sites and component homeomorphisms do not prove the item. No search was invented and no unavailable service was called a negative result. No new-node search obligations arise.

### Tool uses

split_report.tool_uses declares the generic compatible-partition theorem, affine qcqs/spectrality and component-space tools, the ind-etale implication, the affine-map criterion, the existing absolute test construction and condensed-point morphism, and the general slice direct-image formula. These supply technical infrastructure; none replaces a smooth-proper-purity unit step. Maintainer-owned tool_uses was not written.

### Unfinished work

No mathematical part of this split remains. The existing dependencies remain responsible for their own stage-1 splits. The required server dry run and push are performed after writing this report.

## Not duplicates

No new nodes were created. In particular, the overlapping existing lem-zl-affine-component-site-projection is cited, not recreated. The stronger w-local component-ring node was inspected but is not used under missing hypotheses.

## Review by NN

I read the entire B–E delivery-error checklist with the item, its cited statement files and the source paragraphs open. The source for the item is Hemo–Richarz–Scholbach, the paragraph preceding (4.1) and its factorization sentence; the construction and mapping property are the more precise statement and proof after Bhatt–Scholze Lemma 2.2.8. I also read Bhatt–Scholze Lemma 2.1.13 and the paragraph before Lemma 4.2.13. For the supporting implications I checked Stacks proetale.tex lemma-ind-etale-implies (097N), lemma-construct-profinite (097D), properties.tex lemma-quasi-compact-quasi-separated-spectral (094L), and topology.tex lemma-spectral-pi0 (0906). There are no new statements requiring separate source or small-case audits.

Step 1 uses the actual affine-qcqs and qcqs-spectral statements before applying the spectral-component theorem. Affineness is assumed for T and is deliberately imposed on W in the later mapping calculation. Thus compact Hausdorff component spaces are obtained with the exact hypotheses the profinite limit property needs.

Steps 2–3 use the statement, not the proof, of lem-sfb-finite-quotient-fiber-product: its compatible finite partitions and its explicit homeomorphism from the profinite fiber product to the finite-partition limit. I checked the application S1=E, base=S, S2=S, f2=id. The new relative stages are S times over C_i the finite block set A_i; the finite right-hand block coordinates are supplied by the fixed s in S. The index is nonempty and cofiltered by common refinements. The homeomorphism reconstructs e and s, and the coordinate maps give continuity in both directions. I made the determination of the S-coordinate explicit using the same existing theorem for the identity span. This avoids silently assuming a relative-presentation theorem that no cited statement gives.

Step 4 uses the exact first construction clause of lem-zl-affine-component-site-projection. Its affine ind-etale T-scheme and inverse-image sheaf are both in the statement. The implication to weak etaleness is cited separately from lem-weil-pbc-ind-etale-stability, whose statement explicitly gives it. The transition maps have affine source and target; lem-weil-pbc-morphism-affine-schemes-affine therefore applies. No nonexistent w-local or finite-presentation hypothesis is inserted.

Step 5 is the elementary universal-property calculation for that very locally ringed space. The sheaf map is forced by the given map to T, and its stalk maps are the already-local structure maps from T to W. Conversely the second coordinate descends through the component quotient because the target is totally disconnected; the quotient topology gives continuity. This is written out instead of merely citing a fully faithful Yoneda statement or an unstated adjunction. Step 6 applies the defining profinite-limit property to the profinite space pi0(W), whose hypothesis step 1 checked. The affine lifts glue uniquely on an affine cover. Step 7 is uniqueness of these lifts/limits and checks morphisms, identity and composition. These are elementary steps from the supplied construction and the preceding steps, not hidden algebraic lemmas.

Step 8 uses precisely the finite-limit, covering and geometric-morphism clauses of the existing component-site projection statement. Step 9 checks finite coproducts directly on the underlying disjoint union and restricted inverse-image sheaves. This requires no derived-category or cohomological input and includes the empty coproduct.

Step 10 uses the complete existing absolute-test-object statement for T[K], including its presentation independence and maps. The relative calculation for S times K and the finite identity V(S times K_j)=coproduct_{K_j}T identify the two constructions. Naturality is checked by the coordinate formula from step 5, not asserted without a map.

Step 11 cites the exact general slice formula from lem-trf-slice-subtopos-site-presentation, rather than the different existential site-presentation theorem. The latter would not have justified a formula on this fixed profinite site. For p_T I used lem-weil-pbc-profinite-point-pullback together with the actual set-sheaf base-change direct-image definition in def-weil-proetale-inverse-image and the test-object construction in def-sfb-profinite-test-objects. Thus an abelian-only pullback statement is not being used to assert an identity of set topoi. Step 12 compares the sectionwise direct images, with naturality already established, and uses the explicit composition and mate conventions in def-trf-geometric-morphism to obtain the geometric-morphism isomorphism.

I tested T empty (S empty, only the empty relative space, and all schemes empty), E empty over nonempty S, E=S with identity structure map, a finite disjoint union with repeated blocks, and S a point (the ordinary absolute profinite test construction). Empty covering families occur only over the empty profinite space and the cited covering statement permits this case. No connectedness, w-locality, w-contractibility, nonemptiness or Noetherian hypothesis was added. The small index sets are sets of finite clopen partitions inside the stipulated universes.

For B1–B9: there are no new unsplit statements, duplicate definitions, new source tags or leaf declarations to audit; the existing statement is self-contained and unchanged, and TeX escaping and blueprint ancestry have been preserved. B10 was checked by exact-tag and concept searches in the Lean source. For C1–C5 I read every used statement and generated a literal quotation for every step/use pair; I corrected the potential set-versus-abelian citation mismatch before writing the final proof. For C6 the delivery's DAG check verifies acyclicity; the reused component-site node and absolute-test node have no dependency on the item. D1–D5 are addressed by reusing existing construction nodes and carrying the presentation, mapping and factorization arguments in the item. E1–E6 are addressed by the hypothesis and map checks above; no source correction under E7 was necessary. No non-elementary step is longer than 2000 characters. Nothing was compiled, no Lean was written, and the shared repository, source checkouts and launcher files were not modified.

### Delivery diagnostics repaired

The first dry run rejected three verbatim quotation fragments because each was shorter than the required 40 characters. I replaced those fragments with the entire cited statements (affine qcqs, ind-etale stability, and morphisms between affine schemes), so the quotations now display all of the relevant hypotheses and conclusions. No mathematical assertion changed.
