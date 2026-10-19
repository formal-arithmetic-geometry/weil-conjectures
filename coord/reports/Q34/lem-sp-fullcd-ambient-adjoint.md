# Stage-1 report: lem-sp-fullcd-ambient-adjoint

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-fullcd-ambient-adjoint.json: statement, split into ten steps; no Mathlib match for the full assertion.
- dag/nodes/sec-smooth-purity/lem-sp-proetale-higher-image-sums.json: new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-proper-open-derived-support.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for each step/node citation (36 entries).

There are two new nodes and zero Mathlib leaves. Helpers and search records are sandbox-only working material, not DAG deliveries.

## Attachments

None. I searched the project sources for the blueprint id and the relevant notions. AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint, WeilConjectures/SixFunctors/ProEtale/ExceptionalAdjoint.lean:151–153, has a sorry proof. It is not an attachment. The surrounding record does not provide the full coproduct and refinement-coherence assertion either. Upstream master is reference material, not a finished proof. No compiler or Lake command was run.

## Literature wanted

WANTED: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/_section.md, clause (b), for lem-sp-fullcd-ambient-adjoint and lem-sp-proper-open-derived-support. The imported unit record supplies the clause; the named local literature file is absent.

WANTED: literature/stacks-project/sites-cohomology.tex, Tag 0739 (lemma-colim-works-over-collection), for lem-sp-proetale-higher-image-sums. I read the official online statement and proof at https://stacks.math.columbia.edu/tag/0739 . It is the general finite-cover-site continuity input, not an already proved module/direct-image specialization.

WANTED: literature/stacks-project/proetale.tex, Tag 09AG (lemma-jshriek-zero), for the geometric background of lem-sp-proper-open-derived-support. I read the official pro-etale extension-by-zero section at https://stacks.math.columbia.edu/tag/09AD . Tag 09AG proves degree-zero specialization vanishing; it does not assert the new unbounded proper-support lemma.

WANTED: literature/stacks-project/derived.tex, Tag 07K7, and injectives.tex, Tag 0F5Y, for the generic tools used in steps 3 and 5. I checked https://stacks.math.columbia.edu/tag/07K7 and https://stacks.math.columbia.edu/tag/0F5Y against the existing node statements.

## Problems found and corrections

The item's statement is retained. Its source is the conditional clause (b) of sk-prop-sf-existence, not the unconditional étale claim in clause (a), and not the relative constructible statement in clause (c). The item is an auxiliary created node, not the unit's key statement; I have not asserted realization of all three clauses.

The existing étale coproduct statements cannot be applied to the full pro-etale category. Nor does lem-weil-pbc-proetale-module-cohomology-coproducts apply: its coefficients are sheaves of rational algebras, whereas A here is a finite torsion ring. I isolated the actual missing higher-image continuity assertion with finite coefficients. It is stronger than a restatement of the item in one direction (it requires no cohomological-dimension bound), but has only sheaf inputs and classical higher images; it contains no unbounded derived coproduct or adjoint conclusion. Finite-CD passage to arbitrary complexes is proved in steps 1–3.

The existing lem-weil-pbc-proper-open-comparison-proetale assumes Noetherian schemes and K pulled back from a bounded-below étale complex. prop-compactification-coherence-detailed also has an étale-origin restriction and a field base. Neither provides the ambient comparison here. I separated a support assertion with no adjunction/coherence conclusion; steps 6–10 construct the comparison, prove its normalization, and transport Brown's adjunction. This child is an agent-extracted geometric obligation from compactification independence, not a claim that Tag 09AG or the étale proper/open theorem already proves full pro-etale proper base change. The ordinary full pro-etale category is retained throughout; no geometric-stalk conservativity or étale proper base change is silently used.

The Lean FullCD record quantifies over all sheaves after each base change, while def-weil-full-cohomological-dimension clause 2 quantifies over pullbacks from the original source. I do not identify them. The argument needs only clause 1, which both statements supply. The Lean ambient record is also less explicit than the current DAG datum about refinement coherence; the split follows the DAG statement. These are statement-alignment observations, not assertions of finished Lean results.

The self-review repaired two citation gaps: the classical/total comparison now cites lem-sp-kinjective-computes(2); step 6 now cites the sheaf adjunction, exactness, site-localization theorem and Cartesian extension-by-zero comparison rather than treating a derived adjunction as a sheaf statement. All new-node source labels were checked against the source-tag inventory. Every new node remains statement-only as required.

## What remains

The stage-1 split exposes two genuine unsplit mathematical obligations. Their proofs are work for later workers; neither is marked proved or Mathlib. In particular the derived proper-support obligation needs its own geometric proof, and its source field explicitly limits what the related Stacks tag establishes. This delivery does not claim to have formalized those proofs or to have completed the unit. All ten parent steps are explicit assembly arguments conditional on the cited statements.

## Review by Q34

I read the whole unit text in dag/units/sk-prop-sf-existence.json and the ancestor's proof position, then compared the item's finite-coefficient, arbitrary-base, ordinary unbounded domain with each candidate source. I checked the source categories before the proof, since replacing pro-etale by étale or rational coefficients would make both halves look shorter without establishing this item. I read the relevant Stacks continuity, acyclic-complex, Brown, and pro-etale extension-by-zero statements and proofs online; no literature was downloaded into the read-only repository. The two new statements describe precisely the residual site-continuity and geometric-support inputs. Their blueprint provenance points through this item to the ancestor's use of the missing ambient adjunction, with no duplicate blueprint statement found by the DAG and blueprint searches.

For step 1 I opened the Grothendieck-module-category statement, left-exact direct-image statement, FullCD definition, finite-level derived-image definition, bounded-below comparison statement, and quasi-compact-open lemma. They provide respectively enough injectives/Grothendieck exactness, additive left exactness, the bound on all source sheaves, the ordinary total derived image, the identification of its sheaf cohomology with classical R^q, and qc of each j_d. The last lemma is used with base Y: f is finite type over Y and the proper target is separated over Y. It does not assume the original base S is Noetherian or separated. Properness gives qcqs for p.

For step 2 the new higher-image node says exactly that R^q p_* commutes with the specified coproduct, including q=0; the injective-vanishing node says exactly that positive R^q vanishes on injectives. Their combination makes sums of injectives acyclic, without asserting they remain injective. For step 3 I read the degreewise-injective K-injective existence statement, the termwise-derived-coproduct statement, the Grothendieck statement, and the finite-CD acyclic-complex comparison including its naturality clause. All have the required unbounded domain; the latter needs the uniform bound from step 1. Exactness of sums follows explicitly by finite partial sums and exact filtered colimits. The comparison is checked on coprojections, so it is the canonical map, not merely an abstract object isomorphism.

For step 4 I checked that prop-exc-open-adjoint is a full ordinary derived adjunction with finite coefficients, and that extension-by-zero exactness, passage of exact functors to triangulated functors, and unbounded right-derived triangulatedness have the claimed hypotheses. The preservation-of-sums argument is the displayed Hom universal property. Step 5 uses only the precise Brown statement for D of a Grothendieck category, exactness, and preservation of all sums. There is no compact-generation assumption supplied by wishful analogy.

For step 6 I opened the proper/open section lemma: its section really is clopen, not merely open. I checked sheaf-level extension-by-zero adjunction and exactness, exact inverse image in the operations statement, and the localization theorem's evaluation formula. They justify preservation of K-injectivity by open restriction using the written Hom-complex argument. The K-injective existence/computation and definition supply the actual derived calculation. The Cartesian extension-by-zero statement applies to the square with upper map 1_X and lower map b; it has arbitrary complexes and finite coefficients. On the clopen decomposition the section's extension is (K,0), so K-injectivity and Rq_*s_! = identity follow componentwise; no nonproper arbitrary base-change assertion is imported.

In step 7 the new support statement gives exactly the counit required, under the proper refinement and qc-open hypotheses checked earlier. The open/closed statement supplies j^*j_! = identity, while the derived adjunction gives full faithfulness. The alpha map is written as the actual counit after lambda inverse. Step 8 uses the unbounded pro-etale direct-image composition statement, including its identity/associativity normalization. Its equality is checked on the same open component in a common K-injective model and then detected by the full faithfulness just proved. Step 9 uses that same composition theorem and the cofiltered-compactification theorem. The latter assumes a compactifiable separated finite-type morphism with qc open; all are available here. I wrote out both common-refinement independence and the three-object cancellation instead of assuming a single pairwise isomorphism is automatically coherent.

For step 10 I checked the natural-bijection-to-adjunction statement and the current ambient-adjoint definition. The formulas use h composed with t_d inverse; this direction gives eta_d = G(t_d inverse) eta_c and epsilon_d = epsilon_c t_d. Substitution of t_d = t_e theta_u yields exactly the two definition equations, with all G_d chosen to be the same functor. The right comparisons then satisfy identity and composition literally. No FullCD hypothesis is needed for a second compactification: its functor is transported to the chosen one by step 9.

For the new higher-image statement I tested h=identity, q=0, q>0 on injectives, the empty family, the empty scheme and non-Noetherian qcqs morphisms: none requires an omitted CD/Noetherian premise. It is not claimed for arbitrary non-qcqs morphisms. For the support statement I tested identity refinements, X empty, X equal to the entire target and a proper disjoint component outside X; the counit has the expected identity or zero value. It is not inferred from geometric stalks on a full pro-etale topos. These tests do not replace the future proof of either child. For the parent I checked c=0, empty sums, identity and three successive refinements and all adjunction map directions. No explicit counterexample to the retained statements was found, so no STATEMENT-DISPUTED correction was made.

Against delivery-errors B–E I checked: proper new-node schema and ancestry; a genuine lower-level statement rather than a clause copied from the item; all notions introduced and dependencies present; every non-elementary input a cited node whose statement I opened; exact domains and hypotheses in each application; natural canonical maps rather than merely existence; no unsupported use of rational/étale results; no proof sketches in statement-only children; faithful and explicitly agent-authored source attribution; and genuine logged searches. The leanfinder hits were generic Zariski/module pushforwards, condensed-category facts or complex-degree support, not either geometric assertion. Loogle and refined source grep supplied no match. LeanSearch returned unavailable and is recorded as such. I did not manufacture search entries. citations.json copies actual node-statement text verbatim for every uses entry. The same-tag inventory below records all pairs, including those with entirely different conclusions.

## Not duplicates

lem-sp-proetale-higher-image-sums vs lem-sbc-constant-finite-submodule-vanishing: existing statement is étale constant-coefficient vanishing via finite submodules, not pro-etale higher-image sums.

lem-sp-proetale-higher-image-sums vs lem-sbc-prime-quotient-detection: existing statement detects étale constant-sheaf vanishing through prime quotients, not preservation of sums.

lem-sp-proetale-higher-image-sums vs lem-sbc-constant-abelian-higher-image-filtered-colimit: existing statement concerns constant étale abelian coefficients and filtered colimits, not arbitrary pro-etale module sheaves.

lem-sp-proetale-higher-image-sums vs lem-sbc-prime-cyclic-detection: existing statement detects étale higher-image nonvanishing with prime cyclic coefficients.

lem-sp-proetale-higher-image-sums vs lem-sbc-torsion-constant-prime-devissage: existing statement is étale constant-torsion prime devissage, not a pro-etale continuity theorem.

lem-sp-proetale-higher-image-sums vs lem-sc-filtered-colimit-map-zero: existing statement is eventual zero for a map of filtered systems of groups.

lem-sp-proetale-higher-image-sums vs lem-sbc-higher-direct-image-large-filtered-colimit: existing statement has small étale sites, not the small pro-etale sites in the new statement.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact: existing statement gives exact filtered colimits of abelian sheaves, not commutation with higher direct images.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-cohomology-diagram: existing statement constructs the cohomology diagram; it does not assert this higher-image isomorphism.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-limit-cohomology-degree-zero-descent: existing statement is descent from inverse limits of schemes on the étale site in degree zero.

lem-sp-proetale-higher-image-sums vs lem-pbc-constant-mod-cohomology-finsupp-pullback: existing statement decomposes constant étale module coefficients by a basis.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-injective-colimit-acyclic: existing statement is acyclicity for colimits of injectives in étale global-section cohomology.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-short-exact-systems: existing statement constructs short exact coefficient systems for colimit sites.

lem-sp-proetale-higher-image-sums vs lem-pbc-u2-sheafH-large-filtered-colimit: existing statement is filtered-colimit continuity of étale global cohomology.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-limit-acyclic-replacement: existing statement is an acyclic replacement of étale coefficient systems on inverse schemes.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-class-descent: existing statement descends classes to stages of a colimit site.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-acyclic-replacement: existing statement constructs auxiliary acyclic systems, not the new geometric higher-image comparison.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-corrected-lift: existing statement constructs corrected lifts of cohomology classes.

lem-sp-proetale-higher-image-sums vs lem-sc-artin-schreier-base-change-model: existing statement computes an étale curve H1 model via Artin–Schreier.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-connecting-ladder: existing statement concerns connecting ladders of auxiliary coefficient systems.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-boundary-diagrams: existing statement constructs boundary diagrams for colimit sites.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-eventual-vanishing: existing statement is eventual vanishing of classes in the colimit-site argument.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-zero-comparison-injective: existing statement is injectivity of a degree-zero colimit-site comparison.

lem-sp-proetale-higher-image-sums vs lem-pbc-u2-sheafH-large-filtered-colimit-derived: existing statement is continuity of étale cohomology under filtered colimits.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-sites-exact-ladder: existing statement constructs an auxiliary exact ladder.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-limit-cohomology-connecting-ladder: existing statement constructs a connecting ladder for inverse limits of étale sites.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-directed-cohomology-colimit: existing statement is qcqs étale cohomology continuity, not pro-etale higher images.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-limit-affine-eventual-zero: existing statement is eventual zero in affine inverse-scheme étale cohomology.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-colimit-of-sites-cech-complex: existing statement compares finite Čech complexes for a colimit of sites.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-right-derived-filtered-colimit-successor: existing abstract dimension-shift statement assumes prior continuity and acyclicity; it does not supply the geometric pro-etale hypotheses.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-etale-filtered-injective-acyclic: existing statement concerns étale global-section acyclicity of filtered injectives.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-finite-etale-cech-filtered-colimit: existing statement is a finite Čech comparison under evaluation-continuity assumptions, not the missing pro-etale higher-image input.

lem-sp-proper-open-derived-support vs lem-weil-pbc-localization-kan-discrete-lifts: existing statement computes underived Kan extension through discrete lifts, not proper derived preservation of support.

lem-sp-proper-open-derived-support vs lem-weil-pbc-proetale-ringed-localization-sequence: existing statement is the abelian localization sequence, not preservation of its supported subcategory by proper derived image.

lem-sp-proper-open-derived-support vs lem-weil-pbc-proetale-ringed-open-closed: existing statement supplies open/closed abelian identities; it does not assert Ru_* preserves this support.

lem-sp-proper-open-derived-support vs lem-weil-pbc-proetale-shriek-specialization-zero: existing statement is vanishing of degree-zero extension-by-zero sections on special affine objects, not unbounded proper derived support.

lem-sp-proetale-higher-image-sums vs lem-weil-pbc-proetale-module-cohomology-coproducts: existing statement requires rational-algebra coefficients; the new statement uses finite torsion coefficients and higher direct-image sheaves.

lem-sp-proper-open-derived-support vs lem-weil-pbc-proper-open-comparison-proetale: existing statement assumes Noetherian schemes and bounded-below étale-origin K; the new support assertion is on all ordinary unbounded pro-etale K.


## Second reading by Q34

This is an independent second reading. The verdicts and final counts below supersede the first worker's descriptions of two remaining children and its higher-image route; all of the first worker's sections above, including `## Review by Q34`, are retained. Final delivery: one new statement-only node, zero Mathlib leaves, ten parent steps, and 42 verbatim citations.

Sources actually opened: the blueprint's sk-prop-sf-existence/_section.md, clause (b) and its proof, in the read-only mirror `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/`; Stacks `sites-cohomology.tex`, label `lemma-colim-works-over-collection` (0739), `proetale.tex`, label `lemma-jshriek-zero` (09AG), `derived.tex`, label `lemma-unbounded-right-derived` (07K7), and `injectives.tex`, label `proposition-brown` (0F5Y), in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`; Hemo–Richarz–Scholbach, arXiv:2305.18131, Lemma 5.3(1) and its hypercover proof, in that mirror's PDF. The advertised literature paths in this project are missing, but these read-only copies are available; the online 0739 and 09AG statements were also compared. The source-tag inventory `tags/tags` confirms all four Stacks tag/label pairs. HRS Lemma 5.3(1) allows any condensed ring and a common lower bound, precisely the existing continuity node's statement; no rational-algebra hypothesis is present there.

Parent statement: checked against blueprint clause (b), the actual FullCD definition, and the current ambient-datum definition; PASS as a conditional assertion, with the stronger datum's coherence obligations explicitly assembled in steps 6–10. Neither unrestricted proper base change nor unconditional FullCD is asserted. The slopmaster2 declaration `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint` at ExceptionalAdjoint.lean:151–153 was read and contains `sorry`; it is not a finished attachment. The upstream master is reference material only. The Lean FullCD quantification differs from the DAG's second clause, but step 1 uses only their shared all-sheaves vanishing clause on the original proper part.

- Step 1: read the statements of the Grothendieck, left-exact image, K-injective computation, finite-level image, FullCD, small-site, and quasi-compact-open nodes; PASS after spelling out finite type of the proper part over S. The open-qc lemma is applied over Y, whose proper target is separated over Y; no Noetherian or qcqs premise on S or Y is smuggled in.
- Step 2: compared every cited statement with HRS Lemma 5.3(1); REPAIRED. The existing condensed qcqs continuity node applies to the constant condensed ring A and the diagram of finite partial sums in degree zero, with common lower bound zero. The geometric inverse-image statement and constant-sheaf definition identify its coefficient sheaves with the parent's A_T. Finite sums of injective resolutions prove classical additivity; taking the filtered colimit gives the canonical sum comparison. The injective-vanishing statement then supplies acyclicity of sums of injectives. This replaces the redundant new higher-image node.
- Step 3: read degreewise-injective K-injective existence, Grothendieck-derived coproducts, Grothendieck exactness, and finite-CD acyclic-complex computation; PASS. The common bound is c from step 1, with no lower bound on the K_i. Naturality identifies the resulting isomorphism on each coprojection; sums of injectives are used as acyclic terms, without being assumed injective.
- Step 4: read the ordinary unbounded pro-etale open adjunction, exact extension, exact-to-derived functor, and K-injective-derived triangulatedness statements; PASS. The Hom calculation proves preservation of every small coproduct, and the two triangulated functors compose.
- Step 5: read the exact statement of the Brown-right-adjoint node against 0F5Y, injectives-proposition-brown; PASS. The source is D of a Grothendieck category, the target is triangulated, and the functor is exact and preserves sums. No compact-generation premise is needed.
- Step 6: read the proper/open clopen-section, K-injective existence/computation/definition, sheaf adjunction, exact extension, localization, direct-image evaluation, identified-coefficient operations, and Cartesian extension comparison nodes; REPAIRED by writing the clopen sheaf calculation. A site object is covered by its two inverse-image opens with empty overlap, so the sheaf axiom gives the product of sections and componentwise Hom complexes. This proves extension as (I,0) preserves K-injectivity and makes q_*s_!I=I sectionwise. Restriction preserves K-injectivity through its exact left adjoint, as written. The Cartesian square has top identity on X, lower arrow b, and vertical opens s,j_d. This is an open-restriction calculation, not arbitrary proper base change.
- Step 7: checked the residual support node against its exact hypotheses and read the open adjunction; REPAIRED the unnecessary open/closed localization citation. The defining extension presheaf restricts on the localized open site to the original sheaf; its sheafification there is unchanged. Thus the unit is the identity identification, and adjunction proves full faithfulness without choosing an uncited complementary closed subscheme. The new support assertion alone supplies invertibility of the counit, and alpha is its composite with j_!(lambda inverse).
- Step 8: read finite-level composition including identity and associativity, right-adjoint preservation of K-injectives, and the exact module inverse-image adjunction; REPAIRED the common-model justification and displayed the restriction equality. Exact pullback makes successive direct images K-injective, while step 6 handles open restriction. On that model both normalized composites restrict to the identity; full faithfulness from step 7 detects equality. All schemes still have ell invertible and the coefficient is still A_{E,n}, as required by the composition node.
- Step 9: read the direct-image composition and cofiltered compactification statements; PASS. The latter requires only an existing compactification and separated finite type f, with its open quasi-compact by step 1. A further common refinement and successive equalizers remove the choice of common refinement. Computing three comparisons through one such object proves the cocycle by cancellation of the middle comparison.
- Step 10: read the natural-bijection adjunction and the full current ambient-datum definitions; PASS. With t_d:F_d to F_c, the hom bijection uses h composed with t_d inverse, so eta_d=G(t_d inverse)eta_c and epsilon_d=epsilon_c t_d. Substitution of t_d=t_e theta_u gives exactly the two required unit/counit equations with all rho_u identities. FullCD is required only for the distinguished compactification, as the datum states.
- New node lem-sp-proetale-higher-image-sums: compared its entire statement with the existing lem-weil-pbc-condensed-qcqs-pushforward-continuity, the geometric profinite inverse-image node, and constant-sheaf definition; REMOVE as a specialization. Unlike the rational-algebra-only module-cohomology node noticed by the first worker, this existing continuity node allows constant finite coefficients. The specialization and finite-sum argument now occur in step 2, so no replacement child is created.
- New node lem-sp-proper-open-derived-support: compared every hypothesis with the blueprint clause (b) compactification-independence obligation and the related 09AG label lemma-jshriek-zero; PASS as an explicitly agent-extracted residual assertion, not as a theorem stated by 09AG. Added the exact-extension node to make its termwise derived j_! notation self-contained. It introduces proper u, both qc opens, their common source X, the commuting equation, finite A, the ordinary unbounded categories, and the actual counit map. It has no proof/proof dependencies and remains unsplit. The source attribution explicitly distinguishes 09AG's degree-zero assertion from this obligation; no tag is used to define its meaning.

Small-case and hypothesis checks: for step 2 test p=identity, q=0, q>0 on an injective, A a finite field, the zero module, an empty family, and the empty scheme. For the identity the sum comparison is the identity; for the empty family its finite-subset category has the one object empty-set and both sides are zero. These cases do not use FullCD. For the support child test u=identity, X empty, both opens identities, and u with a disjoint proper component outside X; the counit becomes the identity or the map between zero objects as expected. For the parent test c=0, n=1, and three composable refinements; the acyclic-term comparison needs no positive bound, no inverse of the finite coefficient uniformizer is used, and the two map directions in the transported adjunction have the displayed types. No explicit counterexample or ill-typed retained statement was found, so no STATEMENT-DISPUTED correction is warranted.

Existence/duplication audit: I searched the whole DAG by pro-etale/cohomology/colimit/proper-support/refinement vocabulary and by 0739 and 09AG, and ran blueprint_refs ancestor plus whole-blueprint searches for higher direct image, proper support and compactification. The ancestor is cor-exc-base-change-open-immersion-general. The surviving child's from/via/place correctly record its contribution to the missing ambient compactification comparison. Existing lem-amb-unbounded-proper-open-interchange and lem-cbc-open-extended-injective-proper-acyclic concern etale sites; lem-sf-proper-open-comparison-site-normalization, lem-weil-pbc-proper-open-comparison-proetale and the strict-tower comparisons impose etale-origin/bounded-below restrictions, sometimes Noetherian hypotheses. None states the surviving child's full unbounded pro-etale support conclusion. The same-tag inventory above remains valid; its entries about the removed child are historical only. I checked that neither the reused continuity theorem nor the profinite coefficient-pullback theorem reaches this parent through statement or proof dependencies, so their reuse adds no cycle.

Independent Mathlib searches were actually run with msearch.py using different vocabulary: finitary/coherent-site cohomology and filtered colimits, preservation of a derived support subcategory under proper pushforward, the Loogle patterns rightDerived/PreservesColimit and support/pushforward, and source grep for higherDirectImage or extensionByZero support. The returned declarations concern sheaf AB5, cohomology presheaf definitions, underived pushforward functors, t-structure degree support, and quasicoherent pushforward assumptions; none states the geometric proper-support assertion. Exact outputs remain in searches.jsonl; the surviving node records the relevant additional queries and actual results. No Mathlib leaf is justified.

Tool uses for the maintainer to judge and record: the existence unit has no replacement for the general Grothendieck-module, termwise-derived coproduct, finite-CD acyclic-complex, or Brown statements. The cross-unit black boxes used here are lem-pur-ringed-site-grothendieck-abelian, lem-weil-proetale-module-direct-image-left-exact, lem-kun-grothendieck-derived-coproducts, lem-kun-finite-cd-acyclic-complex, lem-grothendieck-derived-brown-right-adjoint, lem-weil-extension-by-zero-exact, lem-weil-extension-by-zero-adjunction, lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-cbc-proetale-extension-zero-base-change, lem-weil-derived-direct-image-composition, lem-cbc-compactifiable-cofiltered, and lem-weil-pbc-proper-open-section. In addition, the genuinely more general lem-weil-pbc-condensed-qcqs-pushforward-continuity is used only on degree-zero finite partial sums, and lem-weil-pbc-profinite-point-pullback only identifies their constant coefficient sheaves. This retains the blueprint's coproducts-then-Brown route; it does not substitute the unrelated rational/etale theorem. Requests are recorded here in prose; the maintainer's tool_uses field has not been written.

Changes made and reasons:

1. Removed the redundant higher-image child and wrote its specialization to degree-zero finite partial sums in parent step 2, using an existing broader theorem.
2. Explained finite type of the proper part over S, clopen sheaf gluing and the K-injective common model, and displayed the normalization equality for composable refinements.
3. Replaced the unnecessary open/closed citation by the direct restriction calculation, avoiding an implicit closed-complement existence premise.
4. Added exact extension to the surviving child's definition dependencies and preserved its honest, limited source attribution.
5. Recomputed all citations.json entries from the actual retained node statements, updated the split summary, recorded genuine new searches, and moved worker tool-use requests from split_report into this prose for maintainer review.
6. Retained the parent statement and the surviving child's mathematical assertion, all first-worker report sections, and statement-only status of the child. No Lean, compiler, Lake, live-project write, or direct git command was used.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q34 lem-sp-fullcd-ambient-adjoint --no-push` printed `OK (not pushed) deliver/Q34/lem-sp-fullcd-ambient-adjoint at 33481bbdad: preflight passed`. Final delivery is run with the same tool, which repeats preflight on its final commit.
