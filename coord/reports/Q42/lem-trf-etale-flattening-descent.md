# Worker report: lem-trf-etale-flattening-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-flattening-descent.json`: split Stacks 0814 in ten steps; no Mathlib match after two semantic phrasings and the other logged searches.
- `dag/nodes/sec-trace-formula/lem-trf-etale-ideal-local-factor.json`: statement only, Stacks 0813; unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-module-strict-transform-flat-pullback.json`: statement only, flat-pullback compatibility of the quotient construction; unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-relative-flatness-source-cover.json`: statement only, Stacks 02JZ; unsplit, no Mathlib match.
- `citations.json`: exact statement quotations for every node used in every proof step. The whole cited statement is retained so its hypotheses remain visible.
- `searches.jsonl` and `research/*`: actual Mathlib search log, complete returned responses, and sandbox-only preparation scripts. These are research evidence, not additional project nodes.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag and flattening/flatification, strict-transform and etale-ideal concepts found no project declaration giving the item or any of these three new statements. Existing blowup declarations support the existing nodes already cited, rather than attachments for this item. The upstream master checkout was treated solely as reference material.

## WANTED

None. The needed source is present in the Stacks TeX checkout.

## Corrections and scope

The item had a correct statement but no proof. I kept every hypothesis and the conclusion. I replaced the final reference to etale as smooth of relative dimension zero by the existing equivalent etale-morphism definition, which directly exposes the flatness used in the proof. This is a definition-citation normalization, not a changed hypothesis. The unused module finite-presentation statement dependency was removed: neither the item nor 0814 assumes finite presentation or finite type for the module. Pullback and fibre-product definitions were added explicitly.

The route remains 0814: stability under admissible blowup, Cartier-boundary reduction, local factorization of centre ideals by 0813, product-ideal domination, flatness descent, and patching affine base charts. The chapter and unit records are unchanged. The blueprint ancestry through the flattening-module node is retained on the item and all children. Searches across the full DAG and the blueprint (`ancestor`, `search flatten`, `search strict transform`, `search push ideal`, `search flat pullback`, `search flatness`, `search 0813`, `search 02JZ`, and etale/base-change keywords) located the existing generic tools and no existing node for the three new statements.

An initial draft would have applied the qcqs module-blowup calculus directly over the original quasi-compact etale bases S_i. Those bases are not assumed quasi-separated. I corrected this by a preliminary refinement by all members of finite affine covers, with inverse-image refinements of the source charts, retaining every chart. The existing qcqs-morphism-permanence statement supplies the needed quasi-compactness and quasi-separatedness facts. This does not strengthen the item.

Minor upstream-record issue reported for maintenance: `lem-trf-module-admissible-blowup-calculus.source.place` labels `lemma-composition-finite-type-blowups` as 080K, while this Stacks checkout's `tags/tags` labels that lemma 080B. The statement of the node is the interface used here, and the actual 080B and 080I source texts support it. I did not edit that other node.

## Not duplicates

lem-trf-module-strict-transform-flat-pullback vs lem-trf-flattening-by-admissible-blowup: the former compares two sheaf quotients under flat maps; the latter asserts existence of a flattening modification and does not assert this comparison (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-module-admissible-blowup-calculus: the former allows a separate flat source/base change; the latter treats composition of blowups and preservation of an already flat module, without this pullback comparison (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-etale-flattening-descent: the new lemma is a general quotient comparison, with no covers, local flattening hypotheses, or existence of a base blowup; the item uses it to prove descent (shared 0814).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-strict-transform-sheaf-kernel: the latter states quasi-coherence, the supported kernel, and the quotient's lack of supported sections; it does not identify the kernel after a flat pullback (shared 080D and 07ZP).

lem-trf-module-strict-transform-flat-pullback vs def-trf-module-strict-transform: the existing node defines the quotient, whereas the new node asserts compatibility of that quotient with flat pullback (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-pur-dnc-affine-blowup-complement: the existing node describes a deformation-to-normal-cone scheme chart, not arbitrary quasi-coherent module strict transforms under flat maps (shared 080D).

No existing source node with 0813 or 02JZ states either of the other new lemmas. In particular `lem-weil-pbc-flat-permanence` is the ring-theoretic 039V statement about a faithfully flat module, not relative flatness of a quasi-coherent module under a flat source map. `lemma-nagata-power-torsion-localization` handles localization, not arbitrary flat pullback. The existing `lem-weil-pbc-etale-covering-base-change` was reused after it was found, so no new etale stability leaf was created.

## Review by Q42

I read `flat.tex`, `lemma-flatten-module-etale-localize` (0814), its immediately preceding `lemma-push-ideal` (0813), and `remark-successive-blowups` (080Y). I also read `divisors.tex` for flat blowup base change (0805), the two-ideal blowup (080A), module strict transform (080D), flat-module strict transforms (080F), composition (080I), extension (080M), and domination (080N); `morphisms.tex` for module base-change flatness (01U8), flat permanence (02JZ), etale base change (02GO), and etale flatness (02GS); and `properties.tex` for supported sections (07ZP). The chapter, unit record, current main-20261015 unit and ancestor proof were read before splitting. The generic algebraic-geometric lemmas here serve the inherited flattening argument below the fixed unit route.

Step 1 uses the actual statements of `lem-weil-pbc-qcqs-morphism-permanence`, the finite affine cover node, and the affine-scheme-qcqs node, to make every refined local base qcqs. The existing `lem-weil-pbc-etale-composition-cancellation` states that open immersions are etale and that etale morphisms compose; I cited it explicitly to justify the restrictions. The cited blowup base-change comparison identifies the restricted blowup; the new strict-transform comparison gives the restricted module quotient. Both covering assertions remain true because all inverse-image source opens are retained. In particular I did not apply a finite affine subcover of the target as though it automatically covered the source by arbitrarily chosen source charts.

Step 2 cites the etale-cover base-change theorem, which explicitly preserves both etaleness and joint surjectivity, and the quasi-compact-base-change theorem. I opened both statements. The etale definition supplies flatness. `thm-nagata-blowup-flat-base-change` says its constructed comparison is an isomorphism; its definition node is cited alongside it to specify the two objects being identified. The new comparison node applies because both e_i and j_i are flat and the diagrams commute; no cartesian hypothesis on the original diagrams is inserted.

Step 3 cites both the product-blowup theorem and its comparison definition: their statements really identify the iterated blowup with the product-centre blowup. I used the module clause, not the scheme-only `lem-trf-strict-transform-composition`. The module calculus supplies composition and preservation of flatness. Centre supports are tracked through both orders; quotients for identical support agree by the strict-transform definition. This supplies stability of the local hypotheses rather than quoting that stability as a new lemma restating the item.

Step 4 obtains a finite-type ideal for the complement using the exact qc-open-complement node, and applies the principalization theorem to obtain a locally regular generator after blowup. The calculus states qcqs of the new base and quasi-coherence of the new module. The Cartier-ideal definition gives local generators which are nonzerodivisors. The finite subcover uses the definition of quasi-compactness. This checks the nonzerodivisor hypothesis of 0813 at its point of use; no integrality or Noetherian hypothesis is smuggled in.

Step 5 restricts affine base charts and local centres using the same blowup and strict-transform comparisons and the explicit open-immersion/composition theorem. The affine-etale/ring-etale equivalence node explicitly supplies the ring-map hypothesis. The new 0813 node has exactly the finite-generation, nonzerodivisor, containment of zero loci, and primewise neighbourhood hypotheses in the source. Applying it and taking finite subcovers preserves all original source charts through inverse images. No finite generation of the quasi-coherent module is used.

Step 6 builds the product ideal. Its generators, its unit restriction to U, and its zero-locus union are elementary finite-product calculations. Flat base change identifies its local blowup; the product theorem gives the factorization through each local centre, as a further blowup, rather than an arbitrary dominating map. The extended-centre factors and their union supports are written explicitly.

Step 7 uses the given local flatness and precisely clauses (1) and (2) of the module calculus, then the new flat-pullback comparison. The latter compares the module quotients, not merely their supports or scheme transforms. This is why the definition and the existing scheme strict-transform composition node alone would not have sufficed.

Step 8 descends flatness in two separate operations. First, on stalks, flatness over the local etale base and flatness of that local base over the global base compose by `lem-pc-module-flat-transitive`, whose statement is for an arbitrary flat module. Second, the 02JZ node detects relative flatness after the jointly surjective flat source family. Thus no converse involving the wrong base ring and no sheaf-definition node standing in for a descent theorem is used.

Step 9 expands the locality sentence in 080Y instead of leaving it implicit; the open-immersion/composition theorem also supplies flatness of the open maps used in the comparison. The existing extension construction allows arbitrary qc opens U and V, with local preservation open U intersect V; its theorem states that the extension restricts to the given blowup. I checked this rather than using the weaker sketch statement which requires V to contain U. The product comparison gives further blowups over each extended blowup, not just arbitrary morphisms. The union of centre supports permits the module-composition comparison; the already flat local solution stays flat by clause (2). Flatness is local on the base by the cited stalk definition. Step 10 uses the composite-admissible and module-composition clauses of the same calculus to return to the original S.

For the new pullback node I checked the generality explicitly: the assumptions are e:T to S flat and j:Y to X flat, with a commuting square, not a cartesian square. Flatness of e gives the identification of blowup bases; the induced j^b is the base change of j and is flat. On an affine blowup chart, supported sections are the kernel of N to N[1/a]. Flat extension preserves this kernel, and the tensor product of N[1/a] is the localization of the tensor product of N. Hence the torsion kernels and the quotient maps are identified; these canonical maps agree under restriction and glue. This is a non-elementary sheaf comparison not contained in the definition node or in Mathlib's ordinary tensor-quotient equivalence. I left it statement-only for the next split, as required, with its source places and this argument available to that worker.

For the new 02JZ node the pointwise statement is copied faithfully from the source, with the jointly-surjective-family consequence obtained by taking a preimage of every target point. The source-local flat homomorphism of local rings is faithfully flat even though no global quasi-compactness hypothesis is present. Mathlib's `Module.Flat.iff_flat_tensorProduct` is ordinary base-ring flatness of a module after extension of that base ring; it is not the relative flatness over a third base ring plus the geometric stalk identifications of 02JZ. The retrieved scheme `FlatDescent` results concern flat morphisms rather than arbitrary quasi-coherent modules, so this is not a one-line Mathlib leaf.

Small cases checked: identity e and j, the unit centre, and the zero centre (empty blowup) give the expected comparison for the pullback node. Over k[t], the strict transform of k[t] direct sum k[t]/(t) along (t) kills the second summand; flat base extension preserves that kernel, while dropping flatness need not, so flatness was retained on j. For 0813, A=B and g=1 give I=J and J'=B; a a unit forces J=B; the zero ring has no prime to check. For 02JZ, identity maps give a tautology and an empty jointly surjective family forces the target to be empty. For the item, U=S permits only unit centres and the conclusion follows from source flatness descent; U empty may give an empty blowup and entails no density assumption. Zero modules and empty source schemes cause no problem. No claim assumes a nonempty chart or nonzero rank.

All new nodes are unsplit statements with empty proof and proof_deps. All mathlib_searches entries reproduce actual tool/query text and results saved by msearch.py; each concept was tried in two semantic phrasings, with LeanSearch, Loogle and grep also run. Existing project declarations were inspected read-only. No Lean was written and no compiler or local DAG-validation script was run. Every proof step is below 2000 characters, so there is no long inline step hiding a subsidiary lemma. The three new nodes are independent generic facts, not clauses of the desired existence theorem. Nothing remains unfinished in this split; the new statements deliberately remain queued for later splits.

## Validation

The standalone server checks returned `review_split: PASS` and `check_dag OK: no finding introduced by the sandbox or on its nodes`. The first complete dry run detected combined bracket citations in the new ideal statement; I changed them to individual node brackets and regenerated exact quotations, without changing any mathematical assertion or recorded query.

The full dry run then passed at 3bde16d96b. A final citation audit added the existing open-immersion/etale-composition node explicitly in Steps 1, 5 and 9, so those facts are cited as theorems rather than attributed to the etale definition alone; the final dry run checks this revision.
