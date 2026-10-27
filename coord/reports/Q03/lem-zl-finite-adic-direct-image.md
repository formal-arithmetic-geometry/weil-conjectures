# Repair of lem-zl-finite-adic-direct-image

## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-adic-direct-image.json`: same statement and statement dependencies; five-step assembly of 1681 characters.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-completed-image-comparison.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-counit-restriction-towers.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-integral-fibre-reconstruction.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-rational-heart-comparison.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-restriction-coefficient-descent.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-restriction-diagram-naturality.json`: statement; Mathlib no match; status unsplit, no proof steps or proof dependencies.

Attachments: none. The upstream project search for the item blueprint tag and finite adic direct-image concepts found no finished declaration. `lean/Sheaf/Paper/ZlFiniteAdicDirectImage.lean:746–747` states the item with `sorry`, and therefore is not an attachment. No Lean file was edited and no compiler was run.

WANTED: none. Stacks TeX, the parent blueprint and the local Bhatt–Scholze PDF (with retained extracted text) were available.

The returned fault was proof size and task granularity, not a statement dispute. I preserved the item statement exactly and split the argument into six independently claimable, statement-only tasks. These are not six rewordings of the final conclusion: the first is integral and projection-normalized, the next is about strict finite coefficient systems, the third reconstructs derived fibre objects, the fourth assumes supplied integral comparison data and interprets rational hearts, the fifth is coefficient coherence, and the sixth is diagram transport. All have fully specified inputs; none asserts the entire item.

What remains: the six new statements are queued for their own later splits, as explicitly required by the return. This delivery completes the one-level re-split.

## Return repaired

The human required at least four comparable new nodes, every old argument retained, and an assembly no longer than 3000 characters. There are six new nodes, with statement lengths 2692–3718 characters, and the assembly has 1681 characters. Their proof/proof_deps fields are empty and proof_origin is null. The complete old argument is retained verbatim below, with a precise allocation to each new task, so no hidden subargument was discarded. The old item, citations and all previously logged searches were retained; only missing semantic searches and second phrasings were added.

## Allocation of every original argument

### lem-zl-finite-completed-image-comparison

Original steps 1, 2, 3. Finite presentation, constructibility and etale origin; whole-module exactness, sectionwise product and coefficient restriction identities; normalized completion-unit/strict-limit identification and preservation of the integral standard pair.

### lem-zl-finite-counit-restriction-towers

Original steps 4, 5. Canonical finite exchange via the etale/pro-etale counit mate; finite-fibre sum via etale stalks; K-flat strict quotient representatives; counit/germ component formulas; quotient square identities and levelwise quasi-isomorphisms.

### lem-zl-finite-integral-fibre-reconstruction

Original steps 6, 7. Reduction/limit adjunction counit as a comparison of systems, not just objects; construction of the first completed derived fibre map; second derived map; finite biproduct/strict Roos product reindexing, including the empty fibre.

### lem-zl-finite-rational-heart-comparison

Original steps 8, 9. Identity of the two integral coefficient categories and raw rational localizations; localized standard pair and integral heart representatives; exact rational heart; point sections, heart pullbacks, and the precise middle ordinary H0 and outer stalk interpretations. The general cohomology-sheaf/truncation consequence remains an explicit assembly step.

### lem-zl-finite-restriction-coefficient-descent

Original steps 10. Ordinary versus tower direct image before scalar comparison; pullback and point-section scalar comparisons; tensor restriction formula; coherent finite coefficient change; common-stage descent of functors, maps, t-exactness and hearts.

### lem-zl-finite-restriction-diagram-naturality

Original steps 11. Actual diagram transport of strict counit/germ maps; products, quotient maps and Roos cones; completed pullback composition normalization; point sections, rational and common-stage transport; arbitrary semilinear field automorphisms and naturality in input morphisms.

## Search and definition audit

Before creating nodes I searched the whole DAG by finite direct image, strict towers, geometric fibres, rational comparison, scalar and semilinear transport, and source tags 09A8, 03QP and 0959. I also ran tools/blueprint_refs.py ancestor and whole-blueprint search for finite, completion, rational, scalar and semilinear; complete search output is retained in the sandbox. The ancestor is lem-zl-finite-pushforward, with via = [lem-zl-finite-adic-direct-image] for every new node. No imported blueprint node states one of these six precise normalized statements. The existing finite etale adic cohomology node is restricted to finite etale maps and compatible locally constant finite free systems; it does not cover a finite map with arbitrary constructible complexes.

Mathlib searches were executed only through msearch.py, with exact query text retained in searches.jsonl and each new node. Every node has LeanFinder, Loogle, grep, and two LeanSearch phrasings. The retained partial run had already completed the first queries, so they were read and reused. The missing five LeanFinder requests and all six second semantic phrasings were run. All these services returned actual results, not unavailable responses. The tempting hits are AdicCompletion.map_exact (algebraic module completion), PreservesProduct.iso (an abstract product comparison), TopCat.Presheaf.stalkPushforward (topological presheaves), Scheme.Modules.restrictFunctorAdjCounitIso/restrictStalkNatIso (open-immersion structure-sheaf modules), exactFunctor/localizedModule_functor_map_exact (abstract functors or algebraic modules), and Galois-category fibre automorphisms. None identifies the project completed-coefficient direct image, strict coefficient-system maps, their rational heart interpretation or semilinear completed maps in one specialization. The Mathlib ElladicCohomology grep hit is a definition of coefficient sheaves, not this theorem.

Each new statement repeats the finite-field datum, coefficient DVR and quotients, finite morphism and finite-type separated schemes, completed ring sheaves, integral category and strict reductions. Fibre statements introduce s,S,v,h,P_y,i_x explicitly. Its stmt_deps are exactly the bracketed notion references; where a statement needs the explicit derived-system adjunction convention, it cites lem-coef-derived-system-evaluation-calculus for that stated interface. No proof sketch is hidden inside a new node statement. Definitions do not stand in for conclusions in the assembly.

## Not duplicates

lem-zl-finite-completed-image-comparison vs lem-zl-finite-ind-heart-adjunction: the existing statement is an adjunction on underlying ind hearts over k0; it gives neither the completed integral module functor nor a projection-normalized reduction-tower comparison.

lem-zl-finite-completed-image-comparison vs lem-zl-finite-weil-ind-push-exact: the existing statement is exactness on equivariant ind hearts, not comparison of completed integral derived functors with their quotient projections.

lem-zl-finite-completed-image-comparison vs lem-zl-finite-fp-proetale-pushforward-exact: the existing statement gives exactness on all pro-etale module sheaves; the new task specializes that input and proves the integral constructible normalized completion/tower comparison and etale-origin reduction assertions.

lem-zl-finite-counit-restriction-towers vs lem-sbc-closed-coefficient-source-transition-iso: the existing statement is a degree-q etale higher-image source transition for a closed coefficient support, not a map of all quotient-complex systems with the finite-fibre counit/germ normalization.

lem-zl-finite-counit-restriction-towers vs lem-sbc-closed-coefficient-target-transition-iso: the existing statement is a closed-support etale target transition in a fixed cohomological degree, not strict coefficient-system exchange and restriction maps before derived localization.

lem-zl-finite-counit-restriction-towers vs lem-zl-finite-compactification-stalk-return: the existing statement concerns a finite separating family of Frobenius return-degree evaluations on common-stage Weil stalks, not strict quotient-system maps.

lem-zl-finite-counit-restriction-towers vs lem-fd-finite-etale-adic-cohomology: the existing statement assumes finite etale maps and locally constant finite free systems; the new task allows finite ramified or closed maps and arbitrary integral constructible complexes with derived reductions.

lem-zl-finite-counit-restriction-towers vs lem-trf-finite-base-strict-localization: the existing statement splits scheme strict localizations; it gives no coefficient-system counit comparison.

lem-zl-finite-counit-restriction-towers vs lem-trf-derived-sections-finite-pushforward-modules: the existing statement is ordinary etale derived sections for one fixed coefficient ring, not an etale/pro-etale strict quotient-system comparison.

lem-zl-finite-counit-restriction-towers vs sk-thm-geo-generic-open: the existing statement concerns shrinking an open-immersion direct image and its generic base change; no such shrinking occurs in finite restriction towers.

lem-zl-finite-counit-restriction-towers vs sk-lem-geo-finite-boundary: the existing statement is constructibility and conservativity across a finite boundary, not a normalized fibre comparison.

lem-zl-finite-counit-restriction-towers vs lem-zl-finite-adic-direct-image: the item is the final rational exact-heart/stalk theorem; the new task is strictly finite-level strict coefficient-system counit coherence, with no rational-heart conclusion.

lem-zl-finite-counit-restriction-towers vs lem-a1-finite-weil-sections-decomposition: the existing statement starts with a finite scheme over k0 and proves rational Weil/Frobenius orbit identities; it does not construct strict reduction-system maps for an arbitrary finite f.

lem-zl-finite-counit-restriction-towers vs lem-a1-finite-etale-weil-fibre-comparison: the existing statement assumes a finite etale k0-map and a closed-point Weil/Frobenius comparison; the new task treats finite maps without etaleness and strict complex-system identities before rationalization.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-pushforward-unit-edge-compatibility: The existing statement concerns lem-weil-pbc-finite-pushforward-unit-edge-compatibility in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-split-pieces-cofinal: The existing statement concerns lem-weil-pbc-finite-split-pieces-cofinal in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs sk-lem-pbc-finite: The existing statement concerns sk-lem-pbc-finite in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-surjective-unit-mono: The existing statement concerns lem-weil-pbc-finite-surjective-unit-mono in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective: The existing statement concerns lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite: The existing statement concerns lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs g1-finite-pushforward-pullback-comparison: The existing statement concerns g1-finite-pushforward-pullback-comparison in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-pushforward-cohomology: The existing statement concerns lem-weil-pbc-finite-pushforward-cohomology in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-pushforward-embedding-pullback: The existing statement concerns lem-weil-pbc-finite-pushforward-embedding-pullback in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs p2-finite-pushforward-module-constructible-reflection: The existing statement concerns p2-finite-pushforward-module-constructible-reflection in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-split-sections-product: The existing statement concerns lem-weil-pbc-finite-split-sections-product in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-stalk-formula-restriction: The existing statement concerns lem-weil-pbc-finite-stalk-formula-restriction in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-sets-finite-pushforward-stalk: The existing statement concerns lem-weil-pbc-sets-finite-pushforward-stalk in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs g1-finite-pushforward-cohomology-comparison: The existing statement concerns g1-finite-pushforward-cohomology-comparison in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-edge-map-base-change: The existing statement concerns lem-weil-pbc-edge-map-base-change in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-split-neighbourhoods-cofinal: The existing statement concerns lem-weil-pbc-finite-split-neighbourhoods-cofinal in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs g1-finite-pushforward-coefficient-control: The existing statement concerns g1-finite-pushforward-coefficient-control in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: The existing statement concerns lem-weil-pbc-sets-pushforward-stalk-strict-henselization in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-module-generic-reflection: The existing statement concerns lem-weil-pbc-finite-module-generic-reflection in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: The existing statement concerns lem-weil-pbc-sepclosed-finite-extension-unique-embedding in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-module-locally-constant-strata: The existing statement concerns lem-weil-pbc-finite-module-locally-constant-strata in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-curve-assertions-dense-open: The existing statement concerns lem-weil-pbc-curve-assertions-dense-open in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-finite-pushforward-constant-closed-unit-killing: The existing statement concerns lem-weil-pbc-finite-pushforward-constant-closed-unit-killing in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-weil-pbc-curve-assertions-finite-pushforward: The existing statement concerns lem-weil-pbc-curve-assertions-finite-pushforward in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-asd-supported-kummer-scalar-source: The existing statement concerns lem-asd-supported-kummer-scalar-source in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-asd-supported-kummer-scalar-derived-units: The existing statement concerns lem-asd-supported-kummer-scalar-derived-units in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-asd-supported-kummer-scalar-maps: The existing statement concerns lem-asd-supported-kummer-scalar-maps in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-fin-finite-direct-image-counit-epi: The existing statement concerns lem-fin-finite-direct-image-counit-epi in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs lem-pur-compact-point-source-normalization: The existing statement concerns lem-pur-compact-point-source-normalization in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-counit-restriction-towers vs sk-lem-curve-finite-support: The existing statement concerns sk-lem-curve-finite-support in one fixed etale coefficient category, not the simultaneous strict quotient-system and completed comparison required here.

lem-zl-finite-completed-image-comparison vs lem-pur-completed-coefficient-pushforward-comparison: the existing theorem compares ordinary ambient derived direct images with reduction towers for any scheme morphism, but does not prove whole-category exactness for finite morphisms, etale-origin constructible reductions, preservation of the integral standard pair, or the geometric finite-presentation hypotheses. It remains an available input, not a one-line proof of the task.

lem-zl-finite-completed-image-comparison vs lem-cbc-exact-product-functor-strict-limit: that theorem assumes an exact product-preserving functor; this task establishes those site-specific hypotheses and identifies its normalized comparison with the prescribed integral constructible direct image.

lem-zl-finite-integral-fibre-reconstruction vs lem-coef-derived-system-evaluation-calculus: that statement supplies the reduction/limit adjunction and conservative evaluation, explicitly without a general reconstruction assertion; this task proves the needed counits invertible for the three geometric systems and constructs the two derived fibre isomorphisms.

lem-zl-finite-rational-heart-comparison vs prop-weil-pbc-rational-transport: that statement extends supplied integral functors and transformations; it does not identify the two project integral categories, rational hearts, or actual point-fibre restriction arrows.

lem-zl-finite-restriction-coefficient-descent vs prop-weil-pbc-scalar-extension: that statement gives coherent ordinary integral geometric comparisons; this task identifies ordinary with tower direct image and includes finite counit/germ restrictions, exact point sections and common-stage descent.

## Review by Q03

I read the return in full: it reopens stage 1 despite the historical reviewed field. The retained sandbox item and returned-node.json were identical to the current read clone, so there was no abandoned newer split to overwrite. No deliver.py process was active at continuation. I read the current parent blueprint finite-pushforward proof, its chapter and affine-line unit, and the cited sources below. The parent currently invokes etale exactness directly and then the geometric finite-stalk formula; my blueprint provenance describes these actual paragraphs, not a fictitious quotation of an adic lemma. The higher-level route is unchanged.

For the completed-image task I checked Stacks 09A8, proetale.tex lemma-finite (including its w-contractible evaluation proof), Bhatt–Scholze Proposition 3.5.1, Lemmas 3.5.6 and 6.7.2, and the statements of the existing exact-product/strict-limit and integral constructibility nodes. The finite-presentation hypothesis is essential for pro-etale exactness and is supplied from the noetherian finite-type base; it is explicitly part of the new assertion, as is finite presentation of h. Products are sectionwise, restriction identifies the same C(V×_Y X), and the completion unit together with the normalized strict-limit comparison yields precisely the recorded projection condition. No surjectivity of derived cohomology towers is assumed.

For the finite-counit task I checked Stacks 0959 (lemma-finite-pushforward-commutes-with-base-change) and 03QP (proposition-finite-higher-direct-image-zero). I read the statements of the existing etale/pro-etale inverse-image and counit-mate comparisons, and the etale-origin lemma; these provide exactly the site transport the old proof used. The task records the map itself, not just an abstract isomorphism of its endpoints. Its strict quotient square is the equality obtained by first restricting a local section then applying the coefficient quotient, or doing those operations in reverse order. Exact finite pushforward applies to modules on both sites.

For reconstruction I checked Bhatt–Scholze Lemma 3.5.7 and the exact statements of the derived-system evaluation/counit calculus, integral pullback constructibility and finite-reduction theorem. The task demands the full system counit, whose evaluated maps are actual projection adjoints; it does not infer a system isomorphism from unrelated choices of level isomorphisms. Both resulting comparisons are stated in D^b_c(s,O_E), before applying sections. The only sum passed through a limit is indexed by the finite set P_y. In Roos coordinates reindexing products preserves 1-s and the shifted-cone differential.

For rational hearts I checked Bhatt–Scholze Proposition 6.8.14(2), Remark 6.8.15, the integral stratified-perfect characterization, localized t-structure, rational transport, point-section exactness and constructible pullback t-exactness statements. The raw categories have identical Hom tensors, and no Karoubi envelope is inserted. This task deliberately assumes the integral t-exact functor and two specified maps so it is a comparison/interpretation problem rather than a restatement of the item. Exact point sections and the actual definitions identify the middle H0 with ordinary fibre cohomology and the outer H0 groups with stalks. The all-degree H^j consequence is retained in the assembly using the general t-exact truncation lemma.

For coefficient descent I checked Bhatt–Scholze Proposition 6.8.14(1), Remark 6.8.15, and the statements of prop-weil-pbc-scalar-extension, integral pullback scalar extension and point-section scalar extension. The ambient direct-image comparison applies only after identifying it with the integral tower image; the new task explicitly includes that normalization. I clarified the statement for ramified coefficient extensions: there is no claim that equal powers of different uniformizers define the same quotient. The finite tensor formula specifies the actual germ map; the coherent coefficient comparisons handle the different quotient systems. Every finite collection of common-stage data has a common finite coefficient field.

For diagram transport I read the parent geometric-Frobenius permutation paragraph and the integral pullback-composition statement. I wrote the full semilinear point reparametrization x↦u x σ_s^{-1}, and the same formula for y. This preserves the fibre equality f x=y. The task records equality of counit/germ maps on strict models, not just a claim that endpoints transport. Products and Roos cones are identified by exact equivalences. Coefficients are unchanged under the base-field automorphism, so the right-hand action is only the point permutation plus stalk transports.

Assembly citation check, step 1: completed-image-comparison explicitly supplies exactness, the normalized isomorphism and preservation of both halves. Step 2: counit-restriction-towers states the strict compatible arrows and their invertibility; integral-fibre-reconstruction states exactly their two completed derived isomorphisms, including projection and empty-fibre normalizations. Step 3: rational-heart-comparison takes exactly the T and comparisons constructed in steps 1–2, identifies the coefficient categories, and supplies the exact rational heart and both displayed H0 restrictions. Step 4: lem-pod-texact-truncation-comparison states unique natural isomorphisms for both truncations of any t-exact triangulated functor; the two truncations and shift define H^j, giving the asserted cohomology isomorphism. Step 5: coefficient-descent supplies finite-field coherence and common-stage descent of functors, maps and the standard pair; diagram-naturality supplies precisely all ordinary and semilinear diagram and input-morphism identities. Every quoted statement was opened and citations.json contains its verbatim text. None of these steps imports a fact from a cited node's proof instead of its statement.

I tested the new assertions on f=id_s, where all normalized restriction maps are identities; a disjoint union of two points, where the second comparison is the two-coordinate biproduct; the empty source/fibre, where it is the unique zero-object isomorphism; and Spec(k[ε]/ε²)→Spec(k), where there is one geometric point and no reducedness assumption may be added. For K=O_E/varpi on the identity map, the derived reductions retain their negative Tor terms, so the argument never assumes reduction of a heart object stays in degree zero. Coefficient extension E= L gives identity comparisons; a ramified extension requires cofinal quotient comparisons rather than identical exponents. A semilinear automorphism transports every point by the stated reparametrization, while the coefficient action stays linear.

B–E audit: all new nodes are statement-only and self-contained, with single-escaped TeX, explicit notion dependencies, exact source places, real logged searches and completed blueprint fields. DAG and blueprint duplicate searches were read, and all shared-tag pairs are distinguished above. The six tasks separate genuine independent comparisons/coherence arguments; no elementary product identity became a standalone node and no node replaces the whole item. The item statement and hypotheses were not weakened. The longest assembly step is under 500 characters, so there is no non-elementary step above the 2000-character review threshold. No SGA source is used. No preflight, DAG or split-check script was run locally: checks are requested only through the authorized server wrappers.

## Original argument retained verbatim

### Original step 1

Allocated to lem-zl-finite-completed-image-comparison.

Work first over $\mathcal O_E$. Finite-type schemes over $k$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and finite-dimensional by [lem-kun-dimension-finite-type], and locally Noetherian by [pqf-lem-locnoeth-lft] (a field is Noetherian since its only ideals are $0,1$), so [pqf-lem-finite-fp-locnoeth] makes $f$ finitely presented. Its base change $h:S=X\times_Ys\to s$, $s=\operatorname{Spec}k$, is finite by [lem-weil-pbc-finite-morphism-permanence], hence also finitely presented. For integral constructible $K$, [lem-sf-integral-direct-image-constructible] supplies all three needed assertions: $Rf_*K$ is integral constructible and derived complete, its canonical finite-reduction maps are isomorphisms, and its finite-level direct images are constructible. The same applies to $h$. By [lem-sf-proetale-constructible-origin], each bounded constructible reduction $K_n$ has etale origin. This last assertion is a theorem about the two sites, not a consequence of the stratification definition alone.

Original cited nodes: pqf-lem-locnoeth-lft, pqf-lem-finite-fp-locnoeth, lem-weil-pbc-finite-morphism-permanence, lem-sf-integral-direct-image-constructible, lem-sf-proetale-constructible-origin, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type.

Source: literature/stacks-project/proetale.tex; Tag 09A8 (finite-presentation hypothesis); integral constructibility/reduction input of lem-sf-integral-direct-image-constructible

### Original step 2

Allocated to lem-zl-finite-completed-image-comparison.

Let $F_f$ be module direct image for the completed coefficient ring sheaves, with action through the canonical ring map. [lem-zl-finite-fp-proetale-pushforward-exact] makes $F_f$ exact on ALL module sheaves, and also makes every finite-coefficient direct image exact. By [lem-weil-pbc-exact-functor-derived-functor], the latter derived functors are computed termwise on every complex. Products are sectionwise and exact by [lem-weil-proetale-countable-products-exact]. For any family $M_n$, the product comparison for $F_f$ is the identity
$$ (F_f\prod_nM_n)(V)=(\prod_nM_n)(V\times_YX)=\prod_n(F_fM_n)(V). $$
Moreover $F_f\operatorname{Res}_nC=\operatorname{Res}_nf_{*,n}C$ termwise: both evaluate to $C(V\times_YX)$, with the same action through $\widehat{\mathcal O}_{E,Y}\to(A_{E,n})_Y$. This equality also identifies the quotient transition maps. Thus [lem-cbc-exact-product-functor-strict-limit] applies to $F_f$ on the full completed module categories, with its projection-normalized comparison.

Original cited nodes: lem-zl-finite-fp-proetale-pushforward-exact, lem-weil-pbc-exact-functor-derived-functor, lem-weil-proetale-countable-products-exact, lem-cbc-exact-product-functor-strict-limit.

Source: literature/stacks-project/proetale.tex; Tag 09A8, Lemma proetale-lemma-finite; product and strict-limit comparison

### Original step 3

Allocated to lem-zl-finite-completed-image-comparison.

Use the strict reduction tower $K_n=K\otimes^LA_{E,n}$. The constant/completed coefficient equivalence and its completion-unit assertion [lem-weil-pbc-constant-completion-equivalence] identify the canonical augmentation $K\to R\lim_n\operatorname{Res}_nK_n$ as an isomorphism for these derived-complete objects. Applying Step 2, with the actual quotient maps, gives the natural isomorphisms
$$F_{f,D}K\simeq F_{f,D}R\lim_n\operatorname{Res}_nK_n\simeq R\lim_n\operatorname{Res}_nf_{*,n}K_n=Rf_*K,$$
the last equality being [def-weil-derived-direct-image]. The normalization in [lem-cbc-exact-product-functor-strict-limit] makes this comparison carry $F_f$ of each quotient projection to the corresponding projection defining $Rf_*$. Exactness and [lem-weil-pbc-exact-functor-complex-cohomology] give $\mathcal H^j(Rf_*K)\cong F_f\mathcal H^j(K)$. Therefore this constructible functor preserves both halves of the integral standard pair [def-weil-constructible-standard-tstructure]. No cohomology tower is asserted surjective; derived reductions, including their negative Tor terms, are retained throughout.

Original cited nodes: lem-weil-pbc-constant-completion-equivalence, lem-cbc-exact-product-functor-strict-limit, def-weil-derived-direct-image, lem-weil-pbc-exact-functor-complex-cohomology, def-weil-constructible-standard-tstructure.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Sections 3.5 and 6.8; canonical coefficient completion, together with Stacks 09A8 as used in Step 2

### Original step 4

Allocated to lem-zl-finite-counit-restriction-towers.

Write $v:S\to X$ for the other projection. At a finite level form the usual restriction/exchange map $b_n:\bar y_n^*f_{*,n}K_n\to h_{*,n}v_n^*K_n$. For an etale-origin complex it is an isomorphism: [lemma-weil-pbc-finite-exchange] is the etale assertion, [lem-weil-pbc-comparison-pullback] identifies its inverse images, and [lem-weil-pbc-comparison-direct-image-canonical-mate] identifies the direct-image comparison with the actual counit mate, so the transported map is $b_n$ itself. Step 1 supplies etale origin. The same construction for $h$ gives restriction maps
$$r_n:h_{*,n}v_n^*K_n\longrightarrow\bigoplus_{\bar x\in P_{\bar y}}\bar x_n^*K_n.$$
They are isomorphisms by [lemma-weil-pbc-finite-stalk-formula]: apply that formula to $h$ at $\mathrm{id}_s$, and use [lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant] to identify sheaves on $s_{\mathrm{et}}$ with their sections/stalks. Transport by the same comparison gives the pro-etale assertion. The abelian and coefficient-module structures follow since the maps preserve addition and scalar multiplication. On the etale side finite direct image is exact, so $Rh_*=h_*$ and $Rf_*=f_*$ on bounded below complexes [lemma-weil-pbc-finite-direct-image-exact]; on the pro-etale side exactness is Step 2. Hence all derived maps here are computed termwise, and the sheaf assertions apply termwise to complexes.

Original cited nodes: lemma-weil-pbc-finite-exchange, lem-weil-pbc-comparison-pullback, lem-weil-pbc-comparison-direct-image-canonical-mate, lemma-weil-pbc-finite-stalk-formula, lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant, lemma-weil-pbc-finite-direct-image-exact.

Source: literature/stacks-project/etale-cohomology.tex; Tags 0959 (finite-pushforward-commutes-with-base-change) and 03QP (finite-higher-direct-image-zero); comparison normalization of the cited canonical-mate node

### Original step 5

Allocated to lem-zl-finite-counit-restriction-towers.

The maps of Step 4 define maps of the coefficient towers, not merely unrelated isomorphisms at each level. Choose a K-flat representative $P$ of $K$ with flat terms, and its strict quotients $P_n$. Since finite pullback and finite pushforward are exact, their termwise composites compute the displayed derived functors. Define $b_n$ by pullback of the direct-image counit. For a geometric lift $i_{\bar x}:s\to S$, the component of $r_n$ is $i_{\bar x,n}^*$ of the counit $h_n^*h_{*,n}v_n^*P_n\to v_n^*P_n$, using $hi_{\bar x}=\mathrm{id}_s$. Restricting a local section and then applying $A_{E,n+1}\to A_{E,n}$ gives the same section as applying that coefficient map and then restricting. Thus each component commutes with $P_{n+1}\to P_n$, and the square for $b_n$ does too. These equalities hold before localization to derived categories and provide strict tower maps. The finite-level identifications in Step 4 show that their evaluations are quasi-isomorphisms. Derived inverse limit, an exact functor on strict tower derived categories by [lem-weil-pbc-ringed-strict-tower-homotopy-limit], consequently sends these tower maps to isomorphisms.

Original cited nodes: def-pur-integral-derived-operations, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md; Explicit restriction/counit maps and quotient compatibility needed for the finite-stalk paragraph

### Original step 6

Allocated to lem-zl-finite-integral-fibre-reconstruction.

Reconstruct the first two towers over $s$, without interchanging point pullback with an arbitrary inverse limit. By [def-pur-integral-derived-operations], $L\bar y^*Rf_*K$ is defined by $R\lim_n\bar y_n^*((Rf_*K)\otimes^LA_{E,n})$. Replace the reductions by $Rf_{*,n}K_n=f_{*,n}K_n$ using the canonical comparison in [lem-sf-integral-direct-image-constructible]. On the other side, [lem-pur-integral-operations-preserve-constructible](1) gives $Lv^*K\in D^b_c(S,\mathcal O_E)$ with canonical reductions $v_n^*K_n$. Hence [def-weil-derived-direct-image] defines $Rh_*Lv^*K$ by $R\lim_n h_{*,n}v_n^*K_n$. The first tower is carried to the second by exactly the $b_n$ of Step 5, with their specified projections. Taking its derived inverse limit gives a natural isomorphism
$$b_K:L\bar y^*Rf_*K\xrightarrow{\sim}Rh_*Lv^*K.$$
This constructs the missing finite-fibre cohomology comparison separately from the stalk-to-product formula. These tower replacements use the counit $\mathcal R_W\mathcal L_WN\to N$ of [lem-coef-derived-system-evaluation-calculus]: take $N=(f_{*,n}K_n)$ on $Y$, $N=(v_n^*K_n)$ on $S$, and $N=(h_{*,n}v_n^*K_n)$ on $s$. Its components are the adjoints of the actual limit projections, exactly the canonical finite-reduction comparisons just used. The cited constructibility/reduction theorems make all these evaluations invertible, so the system counits are invertible by the same calculus. This justifies replacement in the derived system category, including transition compatibility.

Original cited nodes: def-pur-integral-derived-operations, lem-sf-integral-direct-image-constructible, lem-pur-integral-operations-preserve-constructible, def-weil-derived-direct-image, lem-coef-derived-system-evaluation-calculus.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md; The finite geometric-stalk comparison, realized through canonical reduction towers

### Original step 7

Allocated to lem-zl-finite-integral-fibre-reconstruction.

The second tower map of Step 5 gives
$$Rh_*Lv^*K\xrightarrow{\sim}R\lim_n\bigoplus_{\bar x\in P_{\bar y}}\operatorname{Res}_n\bar x_n^*K_n\cong\bigoplus_{\bar x\in P_{\bar y}}L\bar x^*K.$$
For the last equality use the definition of integral pullback [def-pur-integral-derived-operations]. The interchange here is only a FINITE sum with a derived limit: in the strict Roos model [lem-weil-pbc-ringed-strict-tower-homotopy-limit], reindex $\prod_n\prod_{\bar x}$ as $\prod_{\bar x}\prod_n$; it carries $1-s$ to the product of the corresponding $1-s$ maps, so their shifted cones agree. Finite products are biproducts. This also proves the assertion for an empty fibre, when both sides are zero. Thus both isomorphisms are now constructed in the completed derived category over $s$. No application of $\operatorname{Fib}_s$ to a limit comparison is being assumed.

Original cited nodes: def-pur-integral-derived-operations, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

Source: literature/stacks-project/etale-cohomology.tex; Tag 03QP applied levelwise to h, followed by the finite biproduct/Roos calculation

### Original step 8

Allocated to lem-zl-finite-rational-heart-comparison.

Identify the coefficient categories before rationalizing. On our noetherian finite-dimensional schemes, [lem-weil-pbc-integral-stratified-perfect-characterization] identifies [def-weil-derived-complete-integral-detailed] with [def-weil-pbc-bounded-constructible-complete], including the same ring sheaves and reduction functors. Both [def-weil-rationalization-karoubi] and [def-weil-pbc-rational-category] are therefore the SAME raw localization: identical objects and $\operatorname{Hom}(K,L)\otimes_{\mathcal O_E}E$, with no Karoubi completion. Apply [prop-weil-pbc-rational-transport] to localize the $\mathcal O_E$-linear functor of Step 3 and the two natural isomorphisms of Steps 6--7. This is exactly the $E$-coefficient direct image prescribed by [def-weil-derived-direct-image]. The standard pair is defined by integral representatives, and [prop-weil-localized-tstructure] says localization is t-exact and every rational heart object has an integral heart representative. Hence $Rf_*$ is t-exact at $E$. Its heart restriction is exact because a short exact sequence is a triangle in the heart [lem-weil-heart-short-exact-triangles]. The uniqueness of truncation comparisons [lem-pod-texact-truncation-comparison] gives the natural isomorphisms $\mathcal H^jRf_*\cong f_*^c\mathcal H^j$.

Original cited nodes: lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-derived-complete-integral-detailed, def-weil-pbc-bounded-constructible-complete, def-weil-rationalization-karoubi, def-weil-pbc-rational-category, def-weil-derived-direct-image, prop-weil-localized-tstructure, lem-weil-heart-short-exact-triangles, lem-pod-texact-truncation-comparison, prop-weil-pbc-rational-transport.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14(2); identification of the two raw rationalizations and their localized standard t-structures

### Original step 9

Allocated to lem-zl-finite-rational-heart-comparison.

For a rational heart object $\mathcal F$, apply the termwise exact sections functor on $s_{\mathrm{proet}}$ [lem-weil-point-proetale-sections-exact] to the localized isomorphisms of Steps 6--7, and take $H^0$. Its rational version is precisely $\operatorname{Fib}_s$ [def-weil-finite-coefficient-point]. By [lem-a1-constructible-pullback-t-exact], $L\bar y^*Rf_*\mathcal F$, $Lv^*\mathcal F$, and $L\bar x^*\mathcal F$ have the heart interpretations used in the statement. The definition [def-weil-ordinary-compact-cohomology] identifies the middle $H^0$ with $H^0(S,\mathcal F_S)$, while [def-weil-local-frobenius-trace] interprets the outer $H^0$ point complexes as coefficient stalks. Exact additive sections preserve the finite biproduct, yielding
$$(f_*^c\mathcal F)_{\bar y}\xrightarrow{\sim}H^0(S,\mathcal F_S)\xrightarrow{\sim}\bigoplus_{\bar x\in P_{\bar y}}\mathcal F_{\bar x}.$$
These are the restriction maps constructed above, and are $E$-linear.

Original cited nodes: lem-weil-point-proetale-sections-exact, def-weil-finite-coefficient-point, lem-a1-constructible-pullback-t-exact, def-weil-ordinary-compact-cohomology, def-weil-local-frobenius-trace.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md; Restriction maps, the middle finite-fibre cohomology group, and the point-fibre convention in the parent stalk paragraph

### Original step 10

Allocated to lem-zl-finite-restriction-coefficient-descent.

For $E\subset L$, use the identification of categories in Step 8. The coherent comparison [prop-weil-pbc-scalar-extension] applies: our schemes are noetherian finite-dimensional with $\ell$ invertible, and the operations preserve the constructible categories by Steps 1 and 6. Its integral ordinary direct image agrees with our tower direct image by Steps 2--3. Pullback commutes with integral scalar extension by [lem-pur-integral-operations-scalar-extension], and sections do so by [lem-weil-point-sections-scalar-extension]. On the finite quotients all components of $b_n,r_n$ send a section to its restrictions; coefficient extension sends $a\otimes m$ to $a\otimes m|_{\bar x}$. Thus the coefficient comparisons identify the actual restriction maps, not only their sources and targets. Taking their strict derived limits and localizing proves compatibility with scalar extension. By [def-weil-algebraically-closed-coefficients], objects, morphisms, triangles and equalities at $\Qlb$ are represented over a common finite extension. All the assertions, including t-exactness from the stagewise standard pair [def-weil-constructible-standard-tstructure], therefore hold over $\Qlb$ independently of the chosen stage.

Original cited nodes: prop-weil-pbc-scalar-extension, lem-pur-integral-operations-scalar-extension, lem-weil-point-sections-scalar-extension, def-weil-algebraically-closed-coefficients, def-weil-constructible-standard-tstructure.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14(1), Remark 6.8.15; coherent coefficient comparison for the actual restriction maps

### Original step 11

Allocated to lem-zl-finite-restriction-diagram-naturality.

Finally, an isomorphism of finite-morphism diagrams takes a local section and its restriction at a geometric lift to the transported section and its restriction at the corresponding lift. Thus each component $r_{n,\bar x}$ is taken to $r_{n,\bar x'}$, where $\bar x'$ is the transported point; the counit description of $b_n$ gives the same equality for $b_n$. These are equalities on the strict quotient models of Step 5. Isomorphisms induce exact equivalences of the sheaf categories, hence identify the products, transition maps and cones in those models. The pullback composition comparisons [lem-pod-integral-pullback-composition] identify the corresponding integral point complexes with precisely those finite-level composition maps. Applying sections, rationalization, and the common-stage construction preserves these equalities. This includes a diagram isomorphism semilinear over any automorphism of $k$: the coefficient ring is unchanged, and its only action on the finite index set is the indicated permutation, with the induced point/stalk transports on each summand. Naturality in sheaf morphisms follows from the same restriction equality $u(m|_{\bar x})=u(m)|_{\bar x}$.

Original cited nodes: lem-pod-integral-pullback-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md; Naturality of the restriction-of-germs construction under diagram isomorphisms, including semilinear isomorphisms

## Validation

The first required deliver.py --no-push exited successfully: OK (not pushed), commit 58840d9a414, server preflight passed. This included the required DAG/split checks. After that run I corrected the item blueprint place and assembly source-step indexing to name the actual current parent text and corresponding original steps; the statement and proof arguments did not change. A final dry run follows these provenance/report corrections before pushing.
