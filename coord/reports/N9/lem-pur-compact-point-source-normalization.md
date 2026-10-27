# Stage-1 delivery: lem-pur-compact-point-source-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-compact-point-source-normalization.json: split, unchanged statement, five proof steps; not a Mathlib leaf.
- citations.json: eighteen verbatim statement quotations, one for every proof-step citation.
- report.md and searches.jsonl: this report and the actual Mathlib searches.

No new nodes; no Mathlib leaves created. The sandbox initially contained only briefing marker files, with no previous node, report, searches, or interrupted delivery process to recover. The node was read from the current live repository. No repository file, Lean file, launcher file or unit record was modified, and no compiler or build was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for compact-point, skyscraper, section-one and normalization terminology. No project declaration states the whole item. The returned structure-sheaf, scalar-class, generic skyscraper and compactification declarations do not provide this ordinary etale module comparison with both specified derived-map identities.

## WANTED

None. All sources needed for the argument are available under literature/stacks-project. No SGA source was used.

## Problems found and corrections

The imported statement is well typed and true under its given assumptions. Its proof was empty. I preserved its hypotheses, its coefficient category, the chosen compactification, its actual counit e, and its prescribed closed unit u. In particular I do not infer an arbitrary rank-one identification or rescale its generator. I construct beta from the constant-section augmentation of an injective resolution, then compute the actual maps.

The finite-pushforward node lem-trf-derived-sections-finite-pushforward-modules already states the resolution-normalized derived comparison needed here, including preservation of injectives. Its base-change clause is not used. The geometric-point vanishing node is about abelian etale sheaves, so I also cite lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison rather than silently treating that as a theorem about module resolutions. Full faithfulness of single complexes is already a Mathlib leaf: lem-weil-pbc-derived-single-fully-faithful. No duplicate or clause-restatement node was introduced.

For step 4 I made the naturality argument explicit using the natural right-derived augmentation of lem-weil-pbc-right-derived-plus-injective. This avoids relying on an uncited assertion about choosing lifts of the unit to injective resolutions. All objects in that application are bounded below, and their derived sections are computed by the same nonnegative injective-resolution recipe as the ordinary unbounded functor in the statement.

The Mathlib searches run with msearch.py include both semantic phrasings, LeanSearch, Loogle and source grep. All services answered. Hits were Zariski structure-sheaf evaluation/restriction, topological skyscrapers, condensed locally constant objects and the product-of-points map; none is this ordinary etale statement. Both semantic search results were inspected, and the relevant topological skyscraper definitions and the local product-points source were read. Searches from the item's earlier creator remain in the item unchanged; the new records are copied from this sandbox's actual log.

Whole-DAG searches covered the source tags 03QP, 03QT, 03QU, 03FD and 0D6E and the point/cohomology, degree-zero, single-complex and finite-pushforward notions. Blueprint searches covered cohomology point, geometric point cohomology, closed immersion, degree zero, finite pushforward, single fully faithful and compact point normalization. The ancestor remains thm-pur-rank-one-thom through lem-pur-origin-class-projective-comparison. There is no blueprint node with the same whole normalized statement.

The assembly realizes the compact source in Step 2 of thm-pur-rank-one-thom, following its geometric-fibre origin-class route. Generic off-unit tools are explicitly listed in split_report.tool_uses: finite pushforward, geometric-point vanishing, constant-sheaf stalks, module/abelian evaluation, enough injectives, degree-zero augmentation and natural right-derived augmentation. None replaces a purity or integration step of the unit.

## Unfinished work

None in the one-level split. Existing cited unsplit nodes remain existing work items; they were neither claimed nor edited here. Server dry-run and delivery results are recorded below after the commands finish.

## Not duplicates

No new node is proposed. In particular the finite-pushforward, module/abelian comparison, geometric-point vanishing and degree-zero full-faithfulness ingredients are reused under their existing ids.

## Review by N9

I read the current item, its source places in etale-cohomology.tex (03QP proposition-finite-higher-direct-image-zero, 03QT theorem-equivalence-sheaves-point, and 03QU lemma-compare-cohomology-point), sites-cohomology.tex 03FD lemma-cohomology-modules-abelian-agree and 0D6E lemma-derived-pushforward-composition, and derived.tex 05TD lemma-left-exact-higher-derived and 06XS lemma-negative-exts. I also read the current blueprint's sk-prop-an unit and thm-pur-rank-one-thom proof, the chapter/unit records, and every cited node's complete statement. This is an agent-written assembly of those general comparisons, not a claim that the blueprint already contains the missing normalization argument.

Step 1 uses the affine quotient characterization in def-weil-closed-immersion and the finite-module definition in def-weil-finite-integral-morphism. The quotient R/I is cyclic, including R/I=0. This is an elementary proof that k is finite, not a new geometric lemma.

Step 2 uses lem-weil-pbc-module-sheaves-enough-injectives to justify a module injective resolution and lem-weil-pbc-left-exact-injective-resolution-degree-zero for its nonnegative augmentation. I checked that lem-trf-derived-sections-finite-pushforward-modules states exactness, preservation of injectives, and the actual equality of complexes of sections normalizing the derived comparison. The source complex A_S[0] is bounded below and k is finite by step 1, so all its hypotheses hold. Properness of q is used only for the supplied compactification; it is not incorrectly substituted for finiteness of k.

Step 3 uses lem-weil-pbc-geometric-point-cohomology at id_S and lem-weil-pbc-constant-sheaf-geometric-stalk to identify actual constant sections with A and show positive abelian cohomology vanishes. The algebraically closed hypothesis is exactly present. The module/abelian evaluation node says explicitly that its comparison is the identity on sections in degree zero; this supplies the module-resolution vanishing without assuming that forgetting modules preserves injectives. Negative cohomology is zero because the chosen resolution is zero in negative degrees. The resulting augmentation alpha is a quasi-isomorphism by the definition in def-weil-abstract-derived-category; beta is its inverse after the finite-pushforward comparison. The Mathlib leaf lem-weil-pbc-derived-single-fully-faithful makes the uniqueness/independence claim an equality of derived maps. No derived isomorphism is replaced by only a list of cohomology isomorphisms.

Step 4 uses the natural transformation explicitly supplied by lem-weil-pbc-right-derived-plus-injective and the actual degree-zero augmentation isomorphism of lem-weil-pbc-left-exact-injective-resolution-degree-zero. I checked def-kun-rgamma-unbounded for the resolution computation, def-weil-pbc-direct-image for the evaluation on the fibre product Y times_Y S, def-weil-pbc-inverse-image for the adjunction unit, and def-weil-pbc-constant-sheaf for the constant-section map. The adjoint identity on k^{-1}A_Y=A_S sends each constant generator a to a; the displayed H^0 computation therefore proves beta t is the identity on every a, not merely an unspecified invertible scalar. The same full-faithfulness leaf promotes it to the required equality in D(A).

Step 5 uses precisely the chosen-compactification candidate of def-amb-etale-compact-support and the assumed isomorphism e. Writing h=RΓ(e) and lambda=(beta h)^{-1} gives h lambda=beta^{-1}; step 4 gives t=beta^{-1}. This is elementary cancellation and does not require a further counit-normalization lemma or compactification-independence theorem. The result therefore concerns the actual counit in the statement.

For delivery-errors B–E I checked self-contained objects and hypotheses, every quotation against the cited statement, all coefficient categories, the union of uses against proof_deps, elementary judgments, possible circularity and clause-restatement splitting. No new nodes make duplicate or new-node-search obligations vacuous. Each non-elementary step is shorter than 2000 characters and carries no hidden comparison: all comparisons used are cited existing statements. Edge cases checked were A=0, j=id, Y=S, disconnected Y, and nonreduced Y. Disconnected Y simply restricts constant sections to the chosen rational point; nilpotents do not affect the affine cyclic quotient argument. No assertion requires Y connected, q smooth, coefficients prime to the characteristic, or A flat over Z. The empty Y case is excluded by the supplied closed immersion from Spec Omega.
