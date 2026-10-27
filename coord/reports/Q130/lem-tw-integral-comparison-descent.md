# Worker report: lem-tw-integral-comparison-descent

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-integral-comparison-descent.json`: statement node, now split in seven steps; not itself a Mathlib leaf. No new nodes or Mathlib leaves.
- `citations.json`: ten verbatim statement excerpts, covering every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log. Other sandbox-only reading/authoring aids are not delivery files.

## Attachments

None. Searched the item id and ordinary/completed-pullback/completion-comparison terminology throughout `lean/WeilConjectures/`; no declaration there states the complete item. `lean/Sheaf/Paper/OrdinaryCompletedIntegralPullback.lean:504` contains `WeilConjectures.ordinaryIntegralCompletionComparison_existsUnique`, but the brief requires attachment declarations under `WeilConjectures/`, and its displayed signature moreover states the normalized existence/uniqueness rather than spelling out every resolution and roof formula. I read its body and the earlier chain-naturality, comparison-on-good and abstract-normalization constructions as proof guidance, without claiming upstream closure.

## WANTED

None. All sources used were available locally.

## What needed repair

The imported item had a complete intended statement and no proof steps. I retained its statement, coefficient map, all statement dependencies and inherited searches. Its Mathlib hits identify the abstract localization tools, but those tools do not construct the strict quotient augmentation or verify its compatibility with the canonical ordinary counit and the completed representative comparison.

I reused `lem-tw-integral-quotient-augmentation` for the strict chain map and its naturality. I reused the already split `lem-weil-pbc-site-derived-tensor-descent` for the localization equivalence on the actual full homotopy subcategory of flat-term K-flat ring-sheaf complexes, rather than introducing another descent lemma. The proof then applies the existing localization universal-property leaf, with identity lifting comparisons after composing by the given counit and lambda. The ambient resolution formula and roof compatibility are written as cancellations of naturality equations.

There is no STATEMENT-DISPUTED correction. Bhatt--Scholze Lemma 6.5.9 is stated for qcqs schemes and Remark 6.8.15 discusses noetherian schemes; neither is misquoted as an ambient arbitrary-scheme normalization theorem. They supply the ordinary-versus-completed context. The proof here is explicitly agent-written from the generic ringed-site resolution/localization results and the existing strict augmentation statement. It makes no constructibility or invertibility claim and does not invoke any SGA source.

## Not duplicates

No new nodes. Whole-DAG keyword searches found the resolving-class localization theorem, strict quotient augmentation, derived pullback and completed-operation comparison already present. Blueprint searches for K-flat, quotient augmentation and completion comparison found no blueprint node stating this exact normalized ordinary-to-completed comparison. The generic natural-transformation localization lemma is already the Mathlib leaf `lem-weil-pbc-localization-universal-property`, not a reason to create another node or mark this entire item a Mathlib leaf.

## Review by Q130

I read the chapter record `sec-purity-real-sheaves`, unit `sk-r-real-linear`, and the current main-20261015 statement/proof of `lem-tw-dual-negation`. Its proof starts with the dual-stalk representation. This item is the already designated coefficient-realization infrastructure below that step; it changes neither the weight argument nor the unit/chapter route. It is not the unit key node, so no unit record was edited. The four off-unit proof tools are declared individually in `split_report.tool_uses` with their roles.

For the item I read Bhatt--Scholze Lemma 6.5.9(4) with its proof and Remark 6.8.15, Stacks sites-cohomology.tex Tags 06YS (`lemma-K-flat-resolution`), 0G7D (`lemma-factor-through-K-flat`), and 06YY (`lemma-derived-base-change`), derived.tex Tag 08TC (`definition-derived-limit`), and categories.tex Tag 04VG (`lemma-properties-left-localization`). I also read Mathlib Localization/Predicate.lean:260-342, particularly `fullyFaithfulWhiskeringLeft`, `liftNatTrans`, and its component formula. The Stacks-derived-limit discussion explicitly warns that a limit in a triangulated category has a nonunique isomorphism; this is why I kept the actual strict cone and zero coordinate instead of arguing from its unshifted projections alone. No new node has a source requiring a separate review.

Step 1 uses the statement of `lem-weil-pbc-site-derived-tensor-descent`: its first conclusion is exactly the equivalence from localization of the full homotopy subcategory of flat-term K-flat complexes to the derived category. I do not substitute its tensor-bifunctor conclusion for unary descent. Composing a localization with this equivalence gives the required localization L by the universal property, which is cited separately. `lem-pc-kflat-resolution` supplies an actual quasi-isomorphism Q to A for every unbounded complex, with both K-flatness and flat terms. Its ringed-site hypothesis applies to the completed ring SHEAF B_Y; constancy is not assumed. Smallness is relative to the module-sheaf universe, and the argument takes a common larger universe, as allowed by the existing site convention.

Step 2 cites the statement of `lem-tw-integral-quotient-augmentation`, opened in full. It gives all of the properties taken here: the actual quotient transitions, naturality for every chain map, and the map into the strict Roos cone with zero shifted coordinate. Its coefficient map c_f and hypotheses are exactly those of this item; the indexing shift from n+1 in the construction definition to n>=1 is only reindexing. Flatness, constructibility and completeness are not added. This step uses a strictly smaller supporting theorem, not a new restatement of a clause of the item.

Step 3 cites the canonical natural counit in `lem-weil-pbc-ringed-topoi-derived-pullback`, the natural comparison isomorphisms in `lem-pur-integral-operations-well-defined`, and the augmentation naturality in the preceding node. I checked all three statements, not their proof internals. The displayed three naturality identities prove the naturality of gamma=lambda inverse composed with q(alpha) composed with epsilon. This also establishes naturality on homotopy classes because every morphism of the full homotopy subcategory has a chain-map representative and its image under q is independent of that representative. There is no tacit claim that all complexes are K-flat or that arbitrary termwise pullback preserves quasi-isomorphisms. The comparison lambda is the given natural one, and epsilon is the canonical counit, not an arbitrarily chosen isomorphism.

Step 4 uses the localization equivalence from Step 1 and the exact natural-transformation lifting statement in `lem-weil-pbc-localization-universal-property`. Its two input functors invert W because they are restrictions of the already defined functors on the derived category. Identity lifting comparisons apply to P_f L and completed P_f L, so the component produced is exactly gamma, in the order written in the statement. Multiplication by lambda gives the requested normalization.

Step 5 uses the same localization node's faithfulness clause: two transformations equal on the restricted good objects are equal. Equality on those objects follows by canceling lambda, which is an isomorphism. I do not infer uniqueness of arbitrary maps into the cone from product projections, and I do not replace the canonical ordinary counit by a different comparison.

Steps 6 and 7 use no additional theorem. Step 6 solves the naturality square for the actual quasi-isomorphism p:Q to A, with the inverse on P_f(qp) on the right. Both resolution expressions equal the single component eta_A; the explicit canonical comparison u=(qp') inverse composed with qp verifies their agreement. Step 7 writes naturality for both legs of a roof Q <- R -> Q' and inverts the quasi-isomorphism leg. This proves the stated compatibility, and changing a roof leaves the represented derived morphism and therefore the naturality identity unchanged. All these steps have fewer than 2000 characters; none conceals a new comparison lemma.

For small cases I checked the zero complex (all augmentation and comparison components are zero), identity resolutions (Step 6 reduces to the prescribed good-complex normalization), repeated resolutions and identity roof legs (the inverse factors cancel), and unbounded complexes (the resolution/localization tools are explicitly unbounded). For f=id the result is the usual strict quotient augmentation into completion; no assertion makes it an isomorphism for a noncomplete ambient object. Empty schemes cause no additional hypothesis and give the corresponding zero module-category case. The argument does not depend on exactness of an arbitrary product functor beyond the completed-operation well-definedness theorem already cited.

Against delivery-errors B--E: no new statement-only or missing-definition issue is introduced; inherited notions and metadata are retained; every non-elementary step cites the statement it uses, with verbatim excerpts in citations.json; elementary steps are explicit equations rather than imported technical lemmas; dependency closure checks found no edge returning to this item; no content was transferred to a new node; coefficient sheaves, source and target of every comparison and the order of composition were checked. The new searches were run with the required command in all four tools and with a second semantic phrasing. I read the hits: abstract localization and Kan-extension results are useful tools already represented in the DAG, whereas projective/injective nth-derived results have different domains and none states this strict sheaf normalization. All services answered; no unavailable service was reported as no match.

## What remains unfinished

Nothing in the one-level split. The reused quotient-augmentation node remains its own queued item. Its existence is a dependency, not a completed Lean proof claim. No Lean file was written and no compiler or Lake command was run.
