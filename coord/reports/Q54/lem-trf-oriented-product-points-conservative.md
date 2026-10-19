# Q54: lem-trf-oriented-product-points-conservative

## Files written

- dag/nodes/sec-trace-formula/lem-trf-oriented-product-points-conservative.json: statement item, split into seven steps; no project attachment or Mathlib match. The repair adds the necessary hypothesis that $T$ is nonempty.
- dag/nodes/sec-trace-formula/lem-trf-finitary-site-enough-points.json: new statement-only input; no Mathlib match for the finite-cover enough-points criterion.
- dag/nodes/sec-trace-formula/lem-trf-oriented-affine-slice-site.json: new statement-only input; no Mathlib match for the oriented slice identification and its finite-cover presentation.
- dag/nodes/sec-trace-formula/lem-trf-etale-topos-points-geometric.json: new statement-only input; no Mathlib match for representing an arbitrary abstract etale-topos point by a geometric point.

citations.json records all sixteen step/node citations as verbatim excerpts. searches.jsonl retains the actual search command results. The three new nodes have four recorded searches each, including different natural-language phrasings. The item's inherited searches are retained and four Q54 searches added. Additional searches for derived conservativity led to reuse of an existing Mathlib leaf, not a new node. There are three new nodes and zero new Mathlib leaves.

## Attachments

None. Searches in WeilConjectures/ for the blueprint tag, oriented-product/vanishing-topos terminology and enough-points terminology did not find a project declaration proving the whole item. The upstream master is reference material only. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/.

## Problems found and corrected

The inherited source attribution to ILO XI 1.8, 2.5 and 2.7 was too coarse. Section 1.8 classifies points, the proof of 2.5 constructs a finite-cover coherent site only under coherent hypotheses, and §2.7 proves a base-change theorem. The repaired proof uses XI 1.10(b) for localization and applies the §2.5 finite-cover construction only to the affine slice, whose small etale topoi and induced maps are coherent. Stacks 00YQ is used only after that presentation, for its enough-points criterion; it is not cited as the source of the affine-slice presentation. This keeps the global schemes arbitrary while making the local hypotheses explicit.

Likewise the existing bounded-below derived-stalk-conservativity node does not give this item's unbounded conclusion. Instead, the proof uses the existing exact-functor/cohomology Mathlib input and the existing unrestricted derived-isomorphism/cohomology Mathlib input. Every degree is tested separately; no convergence or completeness claim is made.

The triple-point classification is separate from enough points: a universal property alone does not make points conservative. No new node restates the item's conservativity assertion or a module/derived clause of it. The chapter and unit are unchanged; this item is not the unit's key node.

## STATEMENT-DISPUTED

The imported statement was false when $T=\varnothing$: there is no geometric point $x$ of $T$, so the family $(z_{x,y,c})$ is empty, while the small etale topos of the empty scheme and its oriented product can still be nontrivial. An empty family cannot be conservative there. I corrected the statement by adding the hypothesis that $T$ is nonempty (equivalently, that $T$ has a geometric point), and retained all other hypotheses and conclusions.

## Source error

The returned report overstated what the sources supplied. ILO XI 2.5 is a coherent-topos lemma whose proof gives the finite-cover pretopology under its coherence hypotheses; it is applied here only after restricting to affine $U,V,W$, where the relevant etale topoi and induced morphisms are coherent. XI 1.10(b) supplies the localization equivalence. Tag 00YQ supplies only the criterion that a small finite-limit site with finite covering refinements has enough points; it does not establish the affine-slice presentation. The item and affine-slice node now record these source roles separately.

## Unfinished work

No unfinished part of this one-level split. The three new nodes are intentionally statement-only, as required for stage 1. Their proofs are not claimed completed. No targets or definitions were changed.

## Not duplicates

lem-trf-finitary-site-enough-points vs lem-trf-oriented-product-points-conservative: the former concerns set sheaves on any small finite-limit site with finite covering refinements; the item concerns explicit geometric triples for arbitrary scheme-oriented products, including modules and unbounded derived categories, and requires affine localization, point classification and gluing beyond that criterion.

lem-trf-etale-topos-points-geometric vs lem-trf-oriented-product-points-conservative: the former represents any abstract point of a single scheme etale topos by a geometric point; the item proves conservativity of specialization triples on a different oriented-product topos, including modules and unbounded complexes. Realization supplies step 1 but no conservativity assertion.

lem-trf-etale-topos-points-geometric vs lem-weil-pbc-sheafification-geometric-stalk: the latter says abelian presheaf sheafification preserves a supplied geometric stalk; it does not represent an arbitrary abstract topos point by a geometric point.

lem-trf-etale-topos-points-geometric vs lem-weil-pbc-sets-sheafification-geometric-stalk: the latter compares a set presheaf with its sheafification at a given geometric point; it does not classify abstract points.

lem-trf-etale-topos-points-geometric vs lem-weil-pbc-extension-by-zero-stalks: the latter computes extension-by-zero stalks inside and outside an open subscheme; it does not classify abstract points.

lem-trf-etale-topos-points-geometric vs lem-fix-geometric-stalk-topos-point: the latter constructs a point from a supplied geometric point (also in the pro-etale setting); it does not assert that every abstract small-etale-topos point arises this way.

lem-trf-etale-topos-points-geometric vs lem-pod-etale-stalk-tensor-scalar: the latter compares tensor products and scalar extension at a supplied geometric stalk; it does not represent abstract points.

lem-trf-etale-topos-points-geometric vs lem-pod-lisse-tensor-and-scalar-extension: the latter concerns constant and lisse sheaves under tensor and scalar operations; it does not represent arbitrary topos points.

lem-trf-etale-topos-points-geometric vs lem-galois-stalk-representable: the latter identifies a representable's stalk with its geometric fibre for a specified geometric point; it does not classify all abstract etale-topos points.

lem-trf-oriented-affine-slice-site vs lem-trf-oriented-product-universal: the universal construction supplies the triple site and universal property, but not its localization at an associated representable or the finite-cover site of an affine slice.

lem-trf-oriented-affine-slice-site vs lem-trf-oriented-affine-neighbourhood-limit: the latter takes a limit of pointed affine triple schemes to describe a strict-local scheme; it does not identify a slice topos or assert a finite-cover site presentation.

The whole DAG and blueprint were searched by tags 00YQ and 04HU and by enough points, oriented products, affine slices/localization, and geometric realization of points. Source-tag overlaps were opened and compared as above. Generic geometric-stalk conservativity on a scheme is insufficient for an oriented product; the geometric-family-conservative Mathlib constructor is also not the converse realization theorem.

## Review by Q54

I read the current main-20261015 local-term-locality proof, paragraphs (1) and (2), and kept its normal-cone specialization route: this auxiliary result supplies pointwise testing for the oriented nearby-cycle comparison. The nearest blueprint ancestor and intervening nodes are recorded in every new node. I read ILO Exposé XI 1.4/1.6/1.8, 1.10(b), and the proof of 2.5, including the localization formulas (1.b) and (1.c), directly in the local PDF; I used 2.5 only for its coherent finite-cover construction on affine slices. For the new finite-cover criterion I read Stacks sites.tex, Proposition criterion-points, Tag 00YQ, including the finite-limit and finite-refinement hypotheses. For the new point-realization node I read etale-cohomology.tex, Lemma points-small-etale-site, Tag 04HU, parts (1) and (2), and its relation to the geometric-stalk point of 04FM. No SGA source is used.

In step 1 I opened the universal-property node: it says existence and uniqueness for a pair of geometric morphisms together with a direct-image 2-morphism. Its orientation is gp2 => fp1, so with g = identity the required arrow is y => f(x), exactly as in the item. The new 04HU node is used only on the two composites with the scheme topoi. Conjugating the structural arrow by the two chosen point isomorphisms gives a triple to which universal uniqueness applies. This does not assume that all topoi have enough points.

In step 2 I checked the existing affine-cover node's statement actually supplies affine etale coverings of every etale object. I checked all three covering types in the universal node. First pulling an affine cover of V back to U gives a type-(a) cover; type (c) then replaces V by V_i because U_i factors through its inverse image. Its second factor is precisely W times_V V_i. Affine coverings of the first and second factors finish the refinement via (a) and (b). The nearby-cycle definition identifies the site inverse image with base change. These are arbitrary coverings; I do not require finite global covers or assert nonaffine overlaps are affine.

For step 3 I checked that the new affine-slice node states both facts used: a small finite-limit presentation with finite covering refinements, and Gamma(j_Z inverse F) = F(Z). Its source's localization equivalence applies to associated representables, so it does not assume the triple site is subcanonical. Its coherent-site argument is applied to affine U,V,W, whose small etale topoi and induced morphisms satisfy the hypotheses of XI 2.5; Tag 00YQ is invoked only after this presentation. Arbitrary global f and g remain allowed because the argument is local on the affine triple. Each slice point composed with j_Z is a genuine global point and hence classified by step 1. The new finite-cover criterion is applied to this small site, with both hypotheses explicitly supplied, not to the whole oriented site. This proves bijectivity only on affine triples at this stage.

Step 4 uses exactly the sheaf equalizer condition in the opened sites definition. I wrote out injectivity on any object first. This lets the surjectivity argument compare lifts on overlaps even if those overlaps are not affine. The resulting inverse is natural because the original map is natural and every component is bijective. This is elementary gluing from the previously established affine-triple cover, not an uncited comparison lemma.

Step 5 uses the module-category definition and constant-coefficient exact inverse image in the nearby-cycle definition. The opened geometric-morphism definition supplies preservation of finite limits, which transports the finite-arity algebraic operations and their equations on underlying sheaves. After step 4, linearity of the inverse follows by applying the injective original map to sums and to multiplication by a section of the coefficient sheaf on the object in question. This proves the module assertion, rather than silently identifying module conservativity with set conservativity.

In step 6 the nearby-cycle definition explicitly allows exact termwise inverse image on unbounded complexes. I opened the exact-functor/cohomology node: its natural isomorphism holds in every integer degree for any exact functor of abelian categories. I also read the derived-category localization definition: cohomology factors through it. The naturality already obtained on complexes therefore passes through inverses of quasi-isomorphisms; no derived limit lemma is concealed. In step 7 the opened unbounded-iso/cohomology node quantifies over every derived morphism and every integer degree, not just chain maps or bounded-below objects. I checked its Mathlib source, DerivedCategory.isIso_iff in HomologySequence.lean. The module category is abelian by the cited module-category node, satisfying its hypothesis. Each cohomology map is detected by step 5, and the criterion finishes the arbitrary derived morphism. The converse directions merely apply a functor to the inverse.

I checked edge cases after the repair: $T=\varnothing$ is explicitly excluded by the corrected hypothesis; $T=\operatorname{Spec}(k)$ and $B=\operatorname{Spec}(k)$ over a separably closed field reduce to the usual stalk-point test; the zero coefficient ring is harmless; empty affine slice objects are handled by the sheaf equalizer argument. No part requires finite type, torsion coefficients or finite cohomological dimension. Non-quasi-compact and non-quasi-separated global schemes are covered locally without demanding finite global covers.

I checked delivery-errors B through E against these files, including the returned E.2 and E.7/C4 points: notions and hypotheses are introduced; source locations are precise; all non-elementary inputs are existing nodes or the three new statements; no cited definition is used in place of an unprovided theorem. Every cited statement was opened, and citations.json contains its actual used clause. The source-tag duplicate comparisons distinguish statements, not just provenance. No new node is an elementary observation or a clause copied from the item. All seven proof steps are shorter than 2000 characters; none hides a comparison that should be split off. The comparison and point-realization theorems are the new nodes instead. The item is marked split, never reviewed, and the new nodes remain unsplit.
