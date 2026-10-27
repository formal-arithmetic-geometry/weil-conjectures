# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-universal-injectivity-criteria.json`: split item; retained its statement, supplied all four implications of Stacks 0CPN in seven steps. No exact project declaration or Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-relative-diagonal-finite-type.json`: one new statement-only prerequisite, Stacks 04XS; unsplit, no Mathlib match.
- `citations.json`: verbatim statement evidence for every proof citation.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the item's blueprint tag, algebraic-stack language and universal injectivity found scheme theorems only. They do not assert fullness on stack fibre groupoids. No compiler or Lake command was run.

## WANTED

None. All mathematical sources needed here are available in the local Stacks source.

## Faults and corrections

The imported item has the complete, correct three conditions of Tag 0CPN, including an arbitrary algebraic-stack base change and lifting the specified isomorphism beta. It had no proof. I retained the statement and its hypotheses.

The inherited blueprint reference had a null ancestor because its creation chain ends at a Lean-module label, not a DAG id. The actual semantic blueprint place is `det-thm-sf-ctf-stability-direct-images`, explicitly named in its inherited place and already used to repair `def-sfb-stable-pointed-moduli-groupoids`. The first dry run rejected using this as the new node's computed ancestor: the helper follows created.item and returns None. I therefore retain the exact helper result (null) in both nodes, as tools/blueprint_refs.py explicitly permits for a broken creation chain, while preserving the precise semantic place in from.place and split_report. No creation history or tool was changed. Read the current `literature/blueprint/latest/` proof (3); this remains a moduli prerequisite under the inherited alteration route, not a replacement of the unit's direct-image argument. No unit or chapter record is changed.

No unfinished part of this split. The new prerequisite intentionally remains statement-only for the next stage-1 worker.

## Searches and reuse

Read the actual results of the recorded msearch invocations. The item was searched with grep, Loogle, LeanSearch and two LeanFinder phrasings. For the new relative-diagonal theorem I ran all four tools, including two semantic phrasings. The hits are scheme diagonal and ordinary categorical representability statements. In particular, I read Mathlib `AlgebraicGeometry/Morphisms/UniversallyInjective.lean` (theorems `universallyInjective_eq_diagonal` and `UniversallyInjective.iff_diagonal`) and `FormallyUnramified.lean` around line 126. Their objects are schemes and the latter also assumes formal unramifiedness; they do not give the algebraic-stack result.

Whole-DAG searches used tag 04XS, `lemma-properties-diagonal`, `lemma-points-cartesian`, diagonal, rational points, Nullstellensatz and maximal ideals; whole-blueprint searches used `universally injective`, `algebraic stack`, `diagonal`, `properties of diagonal`, `diagonal locally`, `locally of finite type`, `rational point`, `Nullstellensatz`, and `maximal ideal`. Reused the existing chart calculus, stack fibre products and point topology, representable-surjectivity test, maximal-ideal leaf, closed-point residue-field lemma and field-point classification. The point-cartesian assertion is a two-line common-field calculation from the definition, so it is a proof step rather than a new node.

## Not duplicates

`lem-sfb-stack-relative-diagonal-finite-type` vs `lem-sfb-representable-stack-diagonal-criterion`: the old node assumes a representable morphism of Deligne--Mumford stacks and gives a scheme-representable monomorphic locally quasi-finite diagonal and separatedness criteria; it does not cover a general morphism of algebraic stacks with stabilizers.

`lem-sfb-stack-relative-diagonal-finite-type` vs `lem-sfb-stack-isom-space-locally-finite-type`: the old node concerns the absolute Isom space of two objects in one stack. The new node concerns the relative diagonal of a map of two arbitrary stacks, with a prescribed image isomorphism. Passing to that relative fibre and proving local finite type is the separate theorem 04XS, not an assertion of the old statement.

`lem-sfb-stack-relative-diagonal-finite-type` vs `lem-sfb-stack-universal-injectivity-criteria`: the new theorem applies to every stack morphism and asserts representability/local finite type, not any of the equivalent universal-injectivity or fullness conditions of the item. It supplies geometric control of the fibre used to prove the difficult implication, rather than replacing that implication.

`lem-sfb-stack-relative-diagonal-finite-type` vs `lem-sfb-relative-inertia-second-diagonal-geometry`: the concurrently created node includes representability of the relative diagonal and inertia/second-diagonal identifications, but does not assert local finite type of the relative diagonal or of its scheme-test fibres. The new 04XS theorem supplies precisely that missing finite-type input for the rational-point argument.

## Review by Q54

I read stacks-morphisms.tex Tag 0CPN (`lemma-universally-injective`) and the preceding definition of universal injectivity, comparing all three conditions word for word. For the single new node I read the full statement and proof of Tag 04XS (`lemma-properties-diagonal`): it is for arbitrary algebraic-stack morphisms, not just representable ones; its scheme-test fibres are algebraic spaces locally of finite type. No additional finiteness or separation hypothesis was inserted. This is strictly a prerequisite, and carries no proof in its new node.

For step 1 I opened the fibre-product node: its statement explicitly gives algebraicity and the triple construction. I opened the groupoid definition, including its pair-of-arrows equation, and the stack-point-topology node, including equivalence after common extension and functorial point maps. The displayed diagonal and projection formulas follow directly. Step 2 is the elementary fact that an injective map with a right inverse is bijective, applied to the first projection; universal injectivity supplies precisely this base change.

For step 3 I opened the representable-surjectivity node and the chartwise calculus node. The former explicitly equates point-surjectivity with surjectivity on EVERY scheme base change, with no flatness/finite-presentation assumption. The latter explicitly preserves surjectivity under arbitrary base change. The new 04XS node supplies representability before these tests are applied. The stated pullback identification uses exactly the arrows of the triple definition: compatible arrows in X and Z are arrows of W. The fibre-product node ensures W and its self-product are algebraic, so all the stack tests are legitimate. Step 4 proves point lifting from the common-extension definition itself and projects a diagonal point to show equality; it does not assume that the point map to the set-theoretic fibre product is a bijection. Step 5 uses the algebraic-closure definition's explicit existence clause and the triple-arrow equation; it really lifts the specified beta.

For step 6 the new diagonal theorem supplies local finite type over K, and the representable-surjectivity node gives a nonempty fibre over the original K. I read the algebraic-space definition: an etale surjective scheme chart exists. The chartwise calculus statement gives every property used to make that chart locally of finite type over K. I opened the finite-type definition to check that a nonempty affine finite-type open can be chosen from its affine cover. I opened the existing maximal-ideal Mathlib leaf (a nontrivial ring has a maximal ideal), and the closed-point residue-field lemma, and read its source algebra.tex Tag 00FV (`theorem-nullstellensatz`) and morphisms.tex Tag 01TB (`lemma-jacobson-finite-type-points`). The lemma is applied to the affine finite-type open V, where a maximal ideal gives a CLOSED point; it is not applied to an arbitrary nonclosed point of T. Finally I opened the field-point classification and read schemes.tex around Tag 01J9: the inverse of K -> kappa(v) really constructs a K-valued point. This avoids any assertion that a nonempty general K-space has a K-point without finite type. In step 7 the pair (u,v) has f(v)=beta f(u), hence v u^{-1} maps exactly to beta; no descent of a mere extension-field isomorphism is silently assumed.

I checked empty source and empty target cases; the implications are vacuous exactly where they should be. A nontrivial stabilizer is allowed: for a classifying stack over an algebraically closed field, fullness onto a point asks for an isomorphism, not uniqueness, so the proof never imposes faithfulness or a monomorphic diagonal. In the opposite direction, a point mapping to a stack with nontrivial automorphisms need not lift every beta, as expected. No quasi-compactness, Deligne--Mumford assumption, representability of f, or finite type of f is used. Only the relative diagonal fibre has the necessary local finite type.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the sources and opened statements. The only new node is self-contained and has no proof sketch or proof dependencies. Every non-elementary geometric input is cited; the field-equivalence, reassociation and arrow calculations are written out. All step texts are below 2000 characters. A dependency traversal found no return path from any cited input to the item. The two off-unit scheme-point inputs are recorded as generic tool uses; the maximal-ideal input is already a Mathlib leaf. No SGA source is used, no target is weakened, and no Lean or repository file was written.

Validation history: the second dry run reported twelve unrelated standing cycle families (none naming the delivered nodes) as introduced findings. A subsequent retry advanced past that check but found a concurrently created 04XS-tag node; I opened it, checked its exact statement, and recorded the difference above.
