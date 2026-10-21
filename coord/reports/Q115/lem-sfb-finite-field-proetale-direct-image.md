# Stage-1 report: lem-sfb-finite-field-proetale-direct-image

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-proetale-direct-image.json`: item, statement, split into seven proof steps. Its statement is unchanged. There are zero new nodes and zero new Mathlib leaves.
- `citations.json`: 17 step/node entries quoting the full verbatim statement of each cited node.
- `report.md`: this report and Q115's self-review. `searches.jsonl` contains the actual search-command results. The extracted PDF text and the sandbox writing script are working material only.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and the pro-etale finiteness notion. `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`, in `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/Stability.lean:155`, assumes `IsSeparated f` (the section context at line 136) and uses an etale-origin bounded-constructibility predicate for sheaves valued in a fixed coefficient category. It therefore does not state the item under the item's hypotheses. Its K-injective/etale comparison implementation is useful reference material, not an attachment. The ordinary etale finiteness results in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/DirectImage.lean` do not themselves state pro-etale intrinsic finiteness.

## WANTED

None. All documents needed here are present in the read clone.

## What was wrong or changed

The imported item was statement-only. I kept its arbitrary-field, possibly nonseparated, finite-field coefficient statement and added a proof. I preserved its source, ancestry, and previous Mathlib search records; appended five actual Q115 search results; and changed only split-owned fields.

The old `blueprint.same_as` entry `lem-sfb-dc-lower-star-preserves` was misleading: that statement uses the separated standing setting and condensed module objects, with several different coefficient rings. It is related to this item, but is not the same statement. I searched the whole DAG and blueprint and set `same_as` to the empty list. The existing ancestor `lem-sfb-dc-hom-preserves` and its specified place and via list are preserved.

There is no statement dispute, and no route change. This item is the ordinary direct-image input extracted below the finite-field internal-Hom finiteness argument. Its proof follows the finite-field case of Bhatt–Scholze Lemma 6.7.2: comparison to the etale site, finite-coefficient etale finiteness, and the direct-image comparison of Lemma 5.4.3. In that specialization take R=A and maximal ideal zero; no adic completion changes the ordinary category. The existing `thm-dg-finite-type-constructibility` is the arbitrary-field, nonseparated etale finiteness input supplied by the current blueprint.

## Unfinished work

None at the stage-1 level of this item. Existing cited nodes remain their own work items where not already finished; this delivery does not split or modify them. No Lean has been written and no compiler, Lake, or build has been run.

## Searches and reuse

The sandbox initially had no node, proof, report, citations, or search log. I copied the current repository item, retaining its previous search records. The exact Q115 commands and result digests are in `searches.jsonl`; these are appended without changing their query text in `mathlib_searches`. The first LeanFinder query concerned pro-etale bounded constructible direct image. The second asked for higher-direct-image finiteness of constructible finite modules. The hits were constructible subsets, general sheaf pushforward, finite-presentation module sheaves, or condensed coefficient facts, not this theorem. LeanSearch returned ordinary pushforward definitions; Loogle and the recorded Mathlib grep returned zero hits. No service was unavailable. No new node was necessary.

For DAG and blueprint reuse I searched the item and its notions, `6.7.2`, `5.4.3`, arbitrary-field finiteness, and constructible comparison. `blueprint_refs.py ancestor` confirmed `lem-sfb-dc-hom-preserves`. Whole-blueprint searches for `direct image`, `finite-field`, `constructible comparison`, `pro-etale ordinary` (also with the accent), and `Noetherian quasi-separated` were read alongside the candidate DAG statements. In particular I reused the general coefficient comparison instead of the coefficient-specialized `lem-sf-proetale-constructible-origin`, whose A=O_E/varpi^n conventions do not directly cover the item without an extra coefficient construction.

## Not duplicates

No new nodes. The nonseparated etale finiteness input, qcqs geometry, comparison equivalences, stratification gluing, and K-injective foundations all already have nodes and are cited directly.

## Review by Q115

I read Bhatt–Scholze Lemmas 5.4.3 and 6.7.2 and Theorem 6.7.1 in the supplied PDF, extracted in the sandbox. Lemma 5.4.3 is a bounded-below comparison and is not an unbounded comparison theorem; the proof explicitly stays in its domain. I also read the current blueprint's `sec-six-functors-basics/sk-prop-sf-cbc/thm-dg-finite-type-constructibility.md` and proof, and the current constructible-comparison unit. The former explicitly has no separatedness requirement and ordinary derived categories. The latter gives the intrinsic discrete Noetherian-coefficient comparison, rather than a completed coefficient category. Stacks sources read were `proetale.tex`, Tags 09AJ, 09AK, 09AL and 09A6; `properties.tex`, Tag 01OY; `morphisms.tex`, the finite-type Noetherian/quasi-separated lemmas; `sites-cohomology.tex`, Tag 07A5; `injectives.tex`, Tags 079H and 079P; and `derived.tex`, Tags 013K, 070J and 070K. There is no new-node source to audit.

For step 1 I opened the full statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-locally-noetherian-quasi-separated`, and `lem-weil-pbc-qcqs-morphism-permanence`. The first gives Noetherianity over Spec k, the second gives quasi-separated schemes, and the third gives a qcqs morphism from the source/target scheme conditions. The ideal argument for a field and the one-point affine base check are written explicitly. Thus no separatedness is smuggled into the comparison hypotheses.

For step 2 I opened `lem-weil-pbc-etale-stratification-local-gluing-core` and `sk-thm-pe-constructible-comparison`. The gluing statement produces actual factorization morphisms of the global strata through local strata, exactly what restriction of a locally constant model needs. Pulling back its covering preserves the same finite constant module model. I checked that quasi-compactness gives a finite affine cover and that a finite field is Noetherian; finitely generated, finite-dimensional, and finite as a set coincide for its modules. This step resolves the local/global convention instead of assuming it. It adds no auxiliary node for that short application of existing gluing.

For step 3 I opened `sk-thm-pe-constructible-comparison` and `lem-pe-coefficient-comparison-derived-functor`. Their statements give, respectively, a bounded constructible etale preimage of K and the actual intrinsic termwise module inverse image commuting with cohomology. These are stronger and more precise inputs than a node merely defining comparison. I verified discreteness and Noetherianity of A and qcqs of T. The descended object G is bounded, hence bounded below; the chosen isomorphism is an ordinary derived isomorphism.

For step 4 I opened `thm-dg-finite-type-constructibility`. Its entire statement is the ordinary etale finiteness theorem with arbitrary k and possibly nonseparated f. I checked that the finite ring A is annihilated by ell and that ell has a nonzero, hence invertible, image in k. Neither a finite base field nor an algebraically closed base was used. This is a genuinely smaller existing etale theorem, not a new node restating pro-etale finiteness.

For step 5 I opened `lem-pur-ringed-site-grothendieck-abelian`, `lem-sfb-grothendieck-k-injective`, and `lem-weil-pbc-kinjective-total-derived`. They give the actual ringed-site module category, K-injective existence for every complex, and existence/computation of the total right derived functor, respectively. The item already fixes the small-site size convention; the ring sheaves here are commutative. The exactness required on the homotopy-category functor is checked by its action on shifts and cones, not inferred from exactness of the underived left exact pushforward.

For step 6 I opened `lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-dplus-injective-representative`, and `def-sfb-right-derived-functor`. The second statement explicitly covers any abelian category with enough injectives, so it applies to pro-etale modules too; I did not apply the narrower etale-only enough-injectives node to the pro-etale site. A bounded-below injective representative is K-injective by that statement. Thus the same representative computes the D+ and full-category direct images as explained in the step. The definition cited here explicitly supplies computation on a K-injective representative, rather than merely naming RF.

For step 7 I opened `prop-weil-pbc-comparison-direct-image`, `lem-pe-coefficient-comparison-derived-functor`, and `sk-thm-pe-constructible-comparison`. The first says exactly nu_V^* Rf_et,* G is isomorphic to Rf_proet,* nu_T^* G, for qcqs f and bounded-below G. The second supplies the displayed cohomology identity; the third supplies constructibility after pullback. The output's finite interval is the interval already supplied by etale finiteness; no absolute cohomological-dimension bound on the field is asserted. Applying Rf_* to the chosen isomorphism alpha supplies the second arrow in the displayed composite. Global stratification is justified by step 2.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files: no new statement-only nodes to duplicate, no elementary fact promoted to a node, no claimed Mathlib match, no proof hidden in a new node, no use of another node's proof as its statement, and no completion or coefficient switch. Every proof citation has a verbatim statement in citations.json. All seven non-elementary steps are shorter than 2000 characters (the longest is 1079), and each uses only the lemmas just identified. The statement dependencies were preserved because they define exactly the notions the item uses. Generic facts from other units are declared with individual reasons in split_report.tool_uses; these implement the finite-field comparison argument within the existing unit, without replacing a unit-level step.

Small-case checks: the zero complex and the empty source have zero direct image. For the identity morphism the conclusion reduces to the same bounded constructible complex. The point case is relative direct image over Spec k, not absolute Galois cohomology, so fields with large absolute cohomological dimension do not contradict boundedness. A nonseparated finite-type scheme (for example the affine line with doubled origin) still satisfies Noetherianity and qcqs; the proof uses the existing nonseparated etale theorem rather than silently compactifying f itself. The forbidden equal-characteristic coefficient case ell=p is excluded; its Artin–Schreier failure is not inadvertently included. These tests required no correction to the item.

The first server preflight asked that step 7 avoid the contextual words “the item’s”. I replaced them with the explicit condition defining B_A(V); no mathematical assertion changed.
