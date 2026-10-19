## Files written

- `dag/nodes/sec-smooth-purity/det-lem-formal-closed-support-stratum-hom.json`: statement; split into five steps; Mathlib searches found no matching theorem. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statements backing every proof-step citation.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for closed-support and stratum/Hom terminology. There is no declaration carrying this statement. The upstream master reference is not treated as completed evidence.

## WANTED

None. The current blueprint, the parallel basics lemma, and the relevant Stacks TeX are locally available.

## STATEMENT-DISPUTED: omitted scope of the closed-support adjunction

The imported statement permits an arbitrary closed immersion, whereas its own cited theorem `det-lem-formal-closed-support-adjunction` explicitly requires a quasi-compact complementary open immersion. Thus the application in the imported first proof step fails hypothesis checking: no argument in the item supplies this premise. This is a missing hypothesis, not a claim that all arbitrary closed immersions have been refuted.

The premise is not automatic. For `X = Spec(k[x_1,x_2,...])` and `Z = V(x_1,x_2,...)`, the complementary open is the union of the `D(x_n)` and is not quasi-compact. Any finite subunion misses a point obtained by setting its finitely many variables to zero and another variable to one. This is an affine X, so the complementary inclusion fails even the relative quasi-compactness required by the adjunction node.

I read Stacks 09BM (`proetale-lemma-closed-immersion-complement-retrocompact-exact`) and 09AH (`proetale-lemma-ses-associated-to-open`): the first requires a retrocompact complement to assert exactness of pro-étale closed pushforward; the second explicitly assumes that the complementary inclusion is quasi-compact. These are also the inputs named in the parallel basics construction of closed support. I corrected the item by adding exactly the quasi-compactness required by its existing adjunction node, rather than assuming a general-proper ambient right adjoint. In the intended standing finite-type/Noetherian setting this hypothesis is automatic. All coefficient stages, all unbounded complexes, all three isomorphisms, and all integer shifts are retained. The statement also makes the existing coefficient, local-projectivity, and Hom conventions explicit; the last displayed equality of groups is written as its canonical isomorphism.

## Existing nodes and duplicate search

Ran `tools/blueprint_refs.py ancestor det-lem-formal-closed-support-stratum-hom`, and whole-blueprint searches for `stratum` and `finite locally projective`; searched all DAG statements for the closed-support, finite-projective, K-injective and derived-Hom notions. Opened `det-lem-formal-closed-support-stratum`, `det-lem-formal-closed-support-derived`, `det-lem-formal-closed-support-sheaves`, and `sk-lem-formal-closed-support` in full.

The parallel `det-lem-formal-closed-support-stratum` states the same formula, recorded under `blueprint.same_as`, but through its two context nodes it assumes that X is a standing scheme. Its imported proof has the same uncited gaps. It therefore does not directly cover the present arbitrary-X/quasi-compact-complement statement. I reused its generic prerequisites, and created no replacement node. The encompassing `sk-lem-formal-closed-support` depends on this item, so citing it would create a cycle. The bounded-below, locally free ordinary-ring node `lem-weil-pbc-ringed-site-locally-free-derived-hom` does not cover our unbounded complexes and locally projective condensed-coefficient modules and is not used. The condensed finite-free derived-Hom node asserts an unspecified exact endofunctor, not the specified dual-tensor expression, so it is also not used.

## Mathlib searches

All searches were run with the prescribed `msearch.py`; the item records exactly those queries, and `searches.jsonl` is the original tool log. Used two semantic phrasings, LeanSearch, two Loogle queries, and two greps. The first Loogle query returned an unknown-identifier diagnostic (not a substantive absence result); the second returned ordinary adjunction declarations. LeanFinder returned light-condensed internal Hom and ordinary scheme-module restriction/pushforward adjunctions. Read the relevant `ihomPoints` source and `Scheme.Modules.restrictAdjunction`: these do not give the pro-étale closed-support/global-derived-Hom formula. LeanSearch's sheafHom hit is Type-valued and its Ext hits do not state the item. The grep's `Topology.LocallyFinsupp.closedSupport` concerns support of functions. No hit is an exact match or one-line specialization.

## Review by Q25

I read the current source file `sec-smooth-purity/sk-prop-sf-localization/sk-lem-formal-closed-support-stratum-hom.md` and its current unit section, the parallel basics stratum/derived/sheaves source files and node statements, and the Stacks passages cited below. The item is a supporting stratum-Hom calculation, not the unit's key node; no unit or chapter record was changed. Its proof remains the closed adjunction, open adjunction, and finite-projective dual calculation. No SGA source was used. There are no new-node sources to review.

Step 1 uses precisely clause (2) of `det-lem-formal-closed-support-adjunction`: its statement explicitly gives global derived Hom, not merely an ordinary derived-category Hom-set adjunction. The corrected statement supplies its complementary-open quasi-compactness and condensed coefficient hypothesis. I did not infer this from a definition of support. The first arrow is obtained by substituting A = u_!L into that clause.

Step 2 uses the actual statements of `def-sfb-module-open-lower-shriek` (additivity and exactness), `def-sfb-module-open-lower-shriek-adjunction` (the supplied module-object adjunction), and `sk-prop-sfb-cartesian-coefficients` (the actual coefficient pullback is exact). Although two ids begin with def, these statements explicitly carry the needed exactness and adjunction data, rather than merely naming a notion. `prop-pur-kinjective-resolutions-exist` applies after the common size convention replaces sites by small skeleta; its conclusion covers arbitrary unbounded module complexes. `lem-weil-pbc-right-adjoint-preserves-kinjective` has exactly the exact-left-adjoint hypothesis satisfied by u_!, and gives K-injectivity of u^*J. I read Stacks 08BJ in derived.tex. The degreewise adjunction commutes with the differential by its naturality, which is written out in the step. There is no comparison with discrete étale coefficients.

Step 3 uses the sheaf-Hom and tensor definitions to construct evaluation. I checked its free case in coordinates, its restriction to a direct summand via the block diagonal map, and the gluing of the inverses. Exactness is checked by sectionwise kernels and local lifting through sheaf epimorphisms, which are expressly in `def-weil-sheaf-of-modules-category`; finitely many lifts can be put on one refinement. Tensoring an acyclic complex then gives locally a summand of a finite sum of that acyclic complex. This proves the K-flatness required by `def-pc-kflat-complex` directly, rather than treating flatness as an uncited theorem. I read the finite-projective calculation in Stacks 08JJ, sites-cohomology-lemma-dual-perfect-complex. This step is elementary finite-sum/summand arithmetic and sheaf gluing, not a newly named lemma.

Step 4 uses `def-pur-derived-internal-hom` for its actual K-injective model, `lem-pur-hom-kflat-into-kinjective` for K-injectivity of that Hom complex, `def-pur-ringed-site-zeroth-hypercohomology` for its explicit unbounded RΓ computation on K-injectives, and `def-pur-sheaf-hom` for global sections being ordinary module morphisms. I read Stacks 0A96 and 08JA in sites-cohomology.tex, including the proof that K-flat-to-K-injective Hom is K-injective. Step 3 verifies L[0] K-flat before invoking the lemma. The natural degreewise evaluation maps identify the differential as well as the terms. Exactness of dual tensor, already proved, permits its termwise use on arbitrary complexes. No bounded-below theorem is used here.

Step 5 uses `lem-weil-pbc-kinjective-hom-derived` in its general abelian-category form, not its optional bounded-below clause, to pass from homotopy classes to derived maps and to compare resolutions. The explicit Hom-complex differential in `def-pur-hom-complex` identifies cocycles and boundaries with chain maps and chain homotopies after shifting, giving every integer q, including negative q. Naturality comes from the actual adjunction and evaluation maps, not a noncanonical choice of an isomorphism.

I checked the cases L = 0, local rank zero, an empty S or Z, u = identity, and i = identity (with empty quasi-compact complementary open). Every map reduces to the zero map between zero objects, or to the usual finite-projective dual formula as appropriate. For K with arbitrarily negative cohomology the proof still uses unbounded K-injective resolutions and the single term L[0], so there is no infinite-product exactness or boundedness assumption. Local direct summands need not be globally free and are not assumed to be. A dependency traversal also exposed that the broad definition node sk-def-sfb-derived-categories leads through constructibility and back to this item. I replaced that statement dependency with def-weil-abstract-derived-category, whose localization definition is all the statement uses, and rechecked every dependency for a path back to this item: none remains. The only correction to hypotheses is the missing complement quasi-compactness described above. Existing generic tool lemmas are declared in split_report.tool_uses; they fill the unit's calculation rather than change its route.

The B–E self-check found no new nodes to audit, no use of an existing proof in place of its statement, no shifted copy of the item created as a child, and no additional literature fact used without a node. citations.json copies the statements actually used. No other worker's node was changed.

## What remains unfinished

Nothing in this one-level split. The cited existing lemmas retain their own stage-1 obligations. A second reader must review and deliver this sandbox; this worker runs only the dry run.

## Second reading by Q25

- Step 1 checked against the blueprint first displayed isomorphism and the full statement of `det-lem-formal-closed-support-adjunction` (clause 2); verdict: the corrected quasi-compact-complement hypothesis supplies the cited premise and the substitution $A=u_!L$ is valid.
- Step 2 checked against the blueprint second-isomorphism paragraph, Stacks Tag 08BJ, and the statements of the open-extension, coefficient-pullback, K-injective-resolution, and right-adjoint preservation nodes; verdict: exactness, adjunction, and unbounded K-injective hypotheses are all present.
- Step 3 checked against Stacks Tag 08JJ and Tag 06YN, the sheaf Hom/tensor/module-category definitions, and the finite-free/direct-summand edge cases; verdict: evaluation, local gluing, exactness, and K-flatness are elementary consequences and no hidden global-freeness assumption occurs.
- Step 4 checked against Stacks Tags 0A96, 08J7, and 08JA and the cited derived-Hom, K-flat-to-K-injective, hypercohomology, and sheaf-Hom statements; verdict: the K-injective Hom-complex computes the full unbounded derived global sections and the evaluation maps are chain-natural.
- Step 5 checked against Stacks Tag 0A8Z and the general K-injective homotopy-to-derived comparison; verdict: naturality and all integer shifts, including negative degrees, follow from the displayed Hom-complex differential.
- New nodes: none; B1--B7 and duplicate/Mathlib searches were vacuous, and all existing cited node statements were opened and matched to their uses.

I initially checked the blueprint field against the generic strict rule, then verified with `tools/blueprint_refs.py` that this item is itself an imported blueprint node (`blueprint.is` equals its id), for which `blueprint.from: null` is required. I therefore retained the worker's correct null value. No mathematical statement, proof step, citation quote, dependency, or source correction was changed.
