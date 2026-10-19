## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-integral-pullback-completed-comparison.json`: statement, split into eleven proof steps; Mathlib verdict no match. No new nodes or Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for every dependency cited by each numbered step.

## Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 source for the blueprint tag, integral pullback and completed pullback found no declaration giving this comparison. The closest integral-coefficient material is background, not a sorry-free declaration of all these clauses.

## WANTED

None. The Stacks sources and Bhatt–Scholze PDF used here are present locally.

## Findings and corrections

The item statement is unchanged. Its use of `Lg^*` means the integral quotient-cone operation, not the ordinary module pullback along the completed ring map. I named the latter `G` only inside the proof to avoid conflating them. The ambient completed-ring module categories remain distinct from the constant-coefficient categories throughout.

The existing proof was empty. A mere appeal to Stacks 099N(5), or an assertion that both towers have the same evaluations, would omit the strict comparison and the normalization of maps. Steps 5–7 instead construct one compatible resolution tower using `[R --t^n--> R]`, whose degree-minus-one transitions are multiplication by t and whose degree-zero transitions are identities. This gives the comparison before taking derived inverse limit. Step 10 derives the requested projection equation in its stated direction. Step 11 writes the shift sign explicitly.

The imported completeness convention only asks for a Roos triangle. Step 3 therefore uses the existing finite-free scalar comparison at L=E to establish invertibility of the *canonical* quotient-cone unit. Step 4 then uses unit-compatible Koszul reconstruction and a signed coordinate isomorphism to identify exactly the intrinsic definition's unit. I did not assume the two completeness conventions were identical by definition.

The ancestor is `lem-a1-finite-map-purity` through the two existing intermediate nodes. Its first proof paragraph uses the finite-stalk formula, for which the parent's geometric-fibre restriction needs this coefficient comparison. The chapter and unit were read; their weight-estimate argument is unchanged, and this item is not the unit's key theorem, so no unit realization fields were edited. Existing generic foundations from other units are individually declared in `split_report.tool_uses`.

## Searches and reuse

The sandbox originally had no node, split, report or search log. I copied the current item once. I searched the whole DAG and current blueprint for integral/completed pullback comparisons and strict tower/limit models, and ran `tools/blueprint_refs.py ancestor` and its search. No blueprint node states this comparison. Existing nodes for normalized Roos comparison, Koszul reconstruction, finite-free completed scalar comparison, K-flat tower replacements and completed pullback shifts cover all the genuine tools. No lemma was created or relabelled from a clause of the item.

All new Mathlib search records come from the actual `msearch.py` log, retained as `searches.jsonl`. LeanFinder was tried with two distinct formulations (adic integral pullback; strict mapping-fiber versus derived inverse limit). The adic hits were ordinary adic completion/period-ring declarations, and the second search returned injective-resolution naturality and derived-category fractions, not this comparison. LeanSearch returned ordinary sheaf pullback, ordinary AdicCompletion and Profinite limits. Loogle returned underived sheaf module pullback and its composition/identity isomorphisms. The broad derived-completion/strict-limit grep had no hits; the more focused pullback grep located `SheafOfModules.pullback` at PullbackContinuous.lean:53 and `pullbackComp` at line 167. I read those declarations and their surrounding definitions: they are underived functors and do not state the item, even by a one-line specialization. The inherited historical grep entry remains untouched.

## Not duplicates

No new nodes. The existing isomorphism-of-schemes pullback comparison is a special geometric case and does not give this arbitrary-map comparison; the adic presentation-transport node compares two presentations of ordinary completed-ring module pullback, not the integral quotient-cone functor with its strict-tower realization. I reuse the existing general strict Roos node rather than creating another cone/limit comparison.

## Review by Q33

I read Stacks `proetale.tex`, Tag 099N (`lemma-pushforward-Noetherian-case`), all five assertions and the proof of (5), and Tag 099M (`lemma-naive-completion`) with its Koszul proof. Those formulas are for constant coefficients; I did not silently apply them as an equality of completed-ring module categories. I also read `sites-modules.tex`, Tag 093M (`lemma-completion-flat`), including its canonical quotient identifications, and `sites-cohomology.tex`, Tag 0941 (`lemma-derived-limit-is-ok`), including the K-injective tower calculation and short exact sequence. I read the Bhatt–Scholze derived-completion discussion around Definition 3.4.10, Lemma 3.4.12, Proposition 3.5.1 and Definition 3.5.2 in the supplied PDF. There are no new nodes whose source needs an additional review.

For Step 1 I opened the coefficient DVR and finite-quotient statements: they give exactly the PID, nonzero uniformizer, finite residue field and finite quotients used. The perfectness assertion is the written two-term free resolution, not an uncited finiteness theorem. For Step 2 I checked that exact sheafification applies on any site and that the constant/completed comparison really asserts both flatness and the projection-normalized quotient. Tensoring the displayed exact sequence is precisely the cited definition of flatness. This proves regularity on both completed sheaves, rather than assuming an arbitrary completed-ring pullback is flat.

For Step 3 the finite-free scalar comparison explicitly includes L=E and the canonical zero-shifted-component map for the imported completeness convention; the strict Roos statement explicitly identifies augmented maps and is natural, and the exact-products statement covers arbitrary ring sheaves on any small pro-etale site. For Step 4 reconstruction explicitly gives c_K kappa_K = comp_K, which permits cancellation. I checked the coordinate map (x,y) -> (-y,x) against both differentials and against the degree-zero augmentation, so the intrinsic unit itself, not merely its target, is identified.

For Step 5 I opened the K-flat resolution statement and the definitions of K-flatness, flat terms and cones. The acyclic-tensor argument proves that every X_n is resolving and that X_n -> P_n is a quasi-isomorphism. All maps come from one P, so the tower map is strict. In Step 6 the diagram replacement lemma applies to the small index category of positive integers, and the resolving-class lemma computes on every object in that class, not just some chosen resolution. The ringed-topos K-flat pullback statement permits any structure map, which is essential here; no isomorphism hypothesis is smuggled in. The target's regularity from Step 2 gives the augmentation quasi-isomorphism after pullback.

For Step 7 I opened the finite constant-ring structure map and exact-pullback statements. Their finite-discrete-ring hypotheses hold by Step 1. The balancing formulas give the same target scalar action because c_g is defined by those finite projections; quotient transition compatibility is written on the actual maps. Thus no identification of a derived strict diagram is inferred merely from pointwise evaluations. Step 8 uses the total strict-tower limit theorem's functoriality and the normalized Roos theorem's natural isomorphism; its exact-products hypothesis is satisfied on T'. All factors are completed-ring-linear. Step 9 uses the stated uniqueness/computation part of the resolving-class theorem and the integral-operation well-definedness statement, together with localization, to descend naturality from the actual representative constructions.

For Step 10 I checked that the normalized Roos theorem says it commutes with projections. Substituting gamma = Rlim(b)^(-1) rho gives p_comp gamma = p_int, hence exactly p_int gamma^(-1) = p_comp as the item asks. In Step 11 I checked the sign (-1)^r on the shifted product coordinate against the cone differential for arbitrary integer r. The K-injective definition makes shifted resolutions legitimate, and the zero-shifted-component inclusion is preserved. I read the completed-pullback triangle lemma's statement and construction of its composite shift: it is the same reduction/tower/limit shift used by this argument, so the desired comparison is with the specified shift, not a newly chosen shift.

I checked K=0, identity g, an empty source or target when the morphism exists, n=1, and shifts r=0, 1, -1. The zero-ring sheaf on an empty site introduces no exception: injectivity and the cone arguments still hold. No boundedness, constructibility, finite Tor amplitude or noetherianity of the schemes was added. The coefficient ring is Noetherian by Step 1; only it needs that property. Each step is below 2000 characters and is a single construction or direct verification, with the principal-resolution computation spread across its actual source and target constructions rather than hidden in a new restatement node. No SGA source, Lean write, compiler, Lake command, live-project write or independent agent was used.

## Unfinished work

None in the stage-1 split. The new proof only cites existing DAG nodes; their independent formalization is outside this item.
