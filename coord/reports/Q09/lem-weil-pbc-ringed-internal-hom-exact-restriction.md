# Stage-1 report: lem-weil-pbc-ringed-internal-hom-exact-restriction

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-internal-hom-exact-restriction.json`: statement; rechecked and split into six steps. Mathlib verdict: no match for the combined unbounded ringed-site assertion. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node used in every numbered proof step.
- `searches.jsonl`: actual msearch invocations. Historical searches already in the item are retained.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id, `ringedInternalHom`, `derivedInternalHom`, and internal/sheaf Hom terminology, and inspected the homological infrastructure returned by the broader search. No project declaration states all the item's clauses. Its inherited `lean` record refers to three declarations in a later stage-2 Sheaf module; this is not an attachment in the named read-only source checkout, and the inherited audit is `none`. Those maintainer-owned records are preserved.

## WANTED

None. All sources needed are present locally. No SGA source was used.

## What was wrong and what changed

The repository item was `unsplit` despite retaining an earlier reviewed proof. The sandbox initially had no node, report, or search log; I copied the current item rather than discarding its existing proof or metadata. The old last step was 2,905 characters and combined the contravariant cone comparison, replacement of the second-variable triangle, K-injective cone closure, the covariant Hom-cone comparison, and shifts. I read those arguments rather than merely dividing the paragraph at arbitrary places.

Two non-elementary chain identifications already have exact DAG statements: `lem-sc-derived-hom-tensor-total` and `lem-sc-hom-complex-mapping-cone`. The revised proof cites them. The old currying argument cited definitions for the sheaf tensor universal property; using the existing chain-level theorem removes that missing theorem citation. Both tensor representatives are now chosen K-flat, so their total tensor computes the stated derived tensor directly, without the old inline cone/tensor quasi-isomorphism argument. The restriction step now cites the theorem that slice restriction is exact.

K-injective cone closure is not a new node: it is the two- or three-line deduction from the existing Hom-into-triangle exactness, shift stability, and definition of K-injectivity. I wrote it as a separate elementary step. The contravariant cone calculation is explicit finite-biproduct linear algebra, with its differential, inverse-rotation map, and boundary sign written down. There is no hidden comparison justified merely by “standard” or “transport”. In the covariant variable the existing cone-isomorphism theorem supplies the substantial comparison; the explicit differential identifies its triangle maps. These are followed by the existing derived shift lemmas. Every step is below 2,000 characters.

The statement, including its small-site and commutative coefficient assumptions, absence of boundedness/finiteness assumptions, naturality, successive-slice compatibility, and both variances, is unchanged. No unit/chapter record or maintainer-owned metadata was modified. This is supporting Hom calculus for the historical completed-pullback ancestor's completion comparison, not a replacement of any geometric step in the proper-base-change unit.

## Sources, searches and reuse

I read `sites-cohomology.tex`, Tags 08J9 (`lemma-internal-hom`), 08JB (`lemma-restriction-RHom-to-U`), 08JC (`lemma-RHom-triangulated`), section 0A8X (`section-hom-complexes`, including `lemma-compose`), and `lemma-restrict-K-injective-to-open`. For cone closure I read `derived.tex`, Tag 090X (`lemma-triangle-K-injective`) and the preceding definition of K-injectivity. The source's omitted details in 08JC are supplied in the steps, rather than cited as an argument.

DAG searches included the tags 08J9/08JB/08JC/090X, `lemma-compose`, `lemma-RHom-triangulated`, K-injective/cone terminology, Hom-cone statements, representable exactness, and all original dependencies. Whole-blueprint searches used `tools/blueprint_refs.py search` for internal Hom, Hom complex, tensor–Hom, and the three source tags; `ancestor` confirmed `def-weil-pbc-completed-pullback` with the existing via chain. No blueprint node states the whole combined assertion. In particular `lem-sf-hom-triangulated` is only the étale constant-coefficient specialization and depends on this item, so cannot be used here. The newly cited currying, covariant cone, Hom exactness and K-injective shift nodes were checked not to depend on the item.

The current Mathlib searches were run only through the prescribed msearch command and retained exactly in the log and JSON. Two semantic phrasings of the whole item returned underived LightCondensed closed structures, sheaf Hom, slice restriction, and generic exact-functor derived triangulation; their signatures do not give unbounded derived internal Hom on an arbitrary ringed small site. I opened `Mathlib/Condensed/Light/Monoidal.lean` (closed instances around lines 52–65) and `Mathlib/CategoryTheory/Sites/SheafHom.lean` to verify the underived scope. The Loogle query combining internalHom and DerivedCategory had no hits; the narrow Homology grep for RHom/derivedInternalHom/ringedInternalHom had no hits. The wider grep returned unrelated name substrings and was not used as evidence of absence. Additional cone-closure searches returned the K-injective definition, shifts, homotopy invariance, bounded-below injective complexes and unrelated factorization cones. They did not replace the direct elementary deduction. No Mathlib leaf is claimed.

## Not duplicates

No new nodes were created. Existing general theorems were reused, and elementary deductions stayed in proof steps.

## Review by Q09

I checked the unchanged statement clause by clause against 08J9, 08JB and 08JC. The smallness requirement is retained because the K-injective resolution node assumes it; the tensor/Hom coefficient sheaf is commutative throughout. The sites are arbitrary small sites, not assumed to have enough points or to be spaces. Restriction means restriction to the slice site, not to an open subset of a space.

Step 1 uses the existence statements of `lem-pc-kflat-resolution` for A and B and `prop-pur-kinjective-resolutions-exist` for I. I opened `lem-sc-derived-hom-tensor-total`: its statement is the full natural chain isomorphism, not a Hom-set adjunction or a definition. `lem-pur-hom-kflat-into-kinjective` supplies exactly K-injectivity of Hom(B,I), and the derived-Hom definition and `lem-pur-rhom-well-defined` permit these representatives. The two tensor definitions say precisely which total complex and which K-flat condition the statement uses. Thus this step does not ask the definition of K-flatness alone to prove a tensor preservation theorem.

Step 2 uses the exactness conclusion of `lem-pur-site-restriction-module-adjunction-exact`, the family-and-differential description in `def-pur-hom-complex`, and the localized-map description in `def-pur-sheaf-hom`. The statement of `lem-pur-kinjective-restrict-localized` explicitly says that termwise slice restriction of a K-injective complex is K-injective. The derived-Hom definition therefore computes both sides. Identity on each displayed family proves the successive-restriction and naturality clauses; neither clause is silently inferred from existence of some isomorphism.

Step 3 invokes the homotopy-category cone triangle from `lem-pur-homotopy-category-triangulated`. The rotated triangle has middle object C(g), and the statement of `lem-weil-pbc-hom-into-triangle-exact` says a map to that object with zero following composite factors through I. The following composite lands in J[1], which is K-injective by the explicitly cited shift node; both outer Hom groups vanish by the K-injective definition. This is a short deduction from the cited statements, exactly the proof indicated by 090X, and is correctly marked elementary. No sheaf infinite-product exactness enters.

Step 4 uses `def-weil-abstract-derived-category` for the fact that any distinguished derived triangle is isomorphic to a localized cone triangle; `def-pur-hom-complex` supplies its differential. I checked the signs: y has degree n-1, the off-diagonal term is (-1)^(n+1)h(x), and multiplication of y by (-1)^(n-1) identifies the result with C(h)[-1]. The boundary in degree n is (0,(-1)^n y), agreeing with precomposition by -p and the signed source-shift map. `lem-pur-homotopy-category-triangulated` and the rotation axiom in the triangulated-category definition give distinguishedness, and Hom into I is the actual derived-Hom model. This calculation proves the contravariant clause rather than relocating that clause to another node.

Step 5 uses the exact bijectivity statement of `lem-weil-pbc-kinjective-hom-derived` to lift the given first derived arrow between J and I. TR3 from the cited triangulated-category definition completes the square; `lem-sf-triangle-morphism-iso` states that identity first two components force the third to be invertible. Step 3 supplies K-injectivity of the actual cone. The statement of `lem-sc-hom-complex-mapping-cone` is valid for arbitrary unbounded module-sheaf complexes and identifies precisely the two covariant Hom cones being used, with no flatness hypothesis. The finite-biproduct differential and its inclusion/projection give the cone triangle before exact localization. Thus all three Hom terms compute the derived functor; no assertion that arbitrary Hom short exact sequences are exact was used.

Step 6 cites the two existing derived-Hom shift statements. I opened both: the first has shift -m in the result when shifting the first argument by m; the second has shift n when shifting the second argument by n. They are natural isomorphisms on the unbounded derived category, without injectivity/flatness/boundedness hypotheses on its objects. The ordinary Hom differential supplies the sign convention in the cone calculations.

I tested the calculations on the zero complex, f=0, identity f (contractible cone), and modules concentrated in degree zero on the one-point site. In particular the shifted Y summand in Hom(C(f),I) is Y[-1], not Y[1]; for f=0 the computed differential becomes the two direct-summand differentials. The formulas also work for negative n because only parity occurs. Empty/zero module sites cause no nonempty-object assumption. Arbitrarily unbounded complexes use products only to define Hom and finite biproducts in the cone step, so no AB4* assertion or finite-generation condition is smuggled in. This review corrected the omitted theorem citations and the oversized compound proof, and did not change the mathematical statement. Every used-node quotation was copied from that node's actual statement into citations.json.

## Unfinished work

No mathematical split obligation remains. Independent maintainer review is external to this delivery. Stage 2/3 work, compilation, and edits of the reference checkouts are outside this task.
