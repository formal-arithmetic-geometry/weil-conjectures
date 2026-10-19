# Stage-1 delivery: lem-cbc-proetale-extension-zero-base-change

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-proetale-extension-zero-base-change.json`: statement node, split into eight proof steps; not a Mathlib leaf. Its statement and all inherited metadata are retained.
- `citations.json`: verbatim statement quotations for all 15 step/node citations, including the hypotheses used.
- `report.md`: this report. `searches.jsonl` is the unmodified msearch-generated evidence. `update_split.py` is sandbox-only preparation material, not a delivered node.

## New nodes

None. Zero new nodes and zero Mathlib leaves.

## Attachments

None. I searched the slopmaster2 project by the exact blueprint tag, the pro-etale extension-by-zero terminology, and base-change declarations. `AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback` in `SixFunctors/ProEtale/BaseChange/WeaklyEtale.lean:196` concerns direct-image base change; `derivedOpenImmersionLowerShriekUpperStarAdjunction` in `Derived/OpenImmersionLowerShriek.lean:70` concerns the derived adjunction. Neither states this item. The inherited `Sheaf...FiniteOpenBaseChangeNormalized` record is stage-2 metadata, not a new attachment to a finished declaration under the specified slopmaster2 `WeilConjectures/` tree. No Lean was written or compiled.

## WANTED

None. All sources needed for this proof are present locally.

## Corrections and source interpretation

The repository already contained an extensive split and old review records, but its current status is unsplit and there was initially no Q50 sandbox item. I copied that existing item, retained its mathematical statement, proof substance, citations and recorded searches, and rechecked them against the current blueprint. No statement correction or change to its target meaning was needed.

The main-20261015 item and proof, now in `sec-six-functors-basics/sk-prop-sf-cbc`, have the same mathematical statement and right-adjoint route as the master source. The old master source and maintainer-owned chapter/unit metadata remain intact. This is not the unit's key statement, so no unit record was written.

The blueprint says the two right adjoints are equal rather than isomorphic. With arbitrary chosen fibre products and small skeleta, canonical isomorphism is the invariant assertion: the explicit projection-preserving maps in step 4 give it. This is a presentation correction in the proof, not a dispute about the item statement. Similarly, the Hom calculation is first done on sheaves; complexes and the unbounded derived interpretation are then handled separately. This avoids silently treating ordinary direct image as derived direct image.

The inherited first and second steps had 2546 and 2289 characters. I separated them into the coefficient adjunctions, the elementary restriction calculation, the extension-by-zero adjunctions, the elementary fibre-product calculation and the ringed localization comparison. There is no hidden general theorem being proved inline: the non-elementary module/localization statements already exist and are cited. All eight resulting steps are shorter than 2000 characters. The explicit canonical-map and inverse formulas and the chain/derived arguments are retained from the prior proof, with their step references updated.

## Mathlib searches

I read the existing searches and ran five additional logged queries with msearch.py: grep, Loogle, LeanSearch and two distinct LeanFinder phrasings. All services answered successfully in this session; earlier unavailable searches remain recorded as such. The grep found no extension-by-zero or shriek declaration in CategoryTheory/Sites. Loogle found two sheaf criteria for base-change-stable precoverages. The first semantic searches found structure-sheaf restriction and pullback results, and the second phrasing found general module pullback composition, adjunction and free-object formulas. I read `Scheme.Modules.restrictFunctorIsoPullback` and `restrictFunctorComp` in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:453,478 and `SheafOfModules.pullbackIso`, `pullbackComp` in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:106,167. They do not state the open extension-by-zero comparison on the small pro-etale site. Thus the item is not a Mathlib leaf.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches found the item itself and related existing nodes. `lem-cbc-extension-zero-base-change`, `sbc-prop-extension-by-zero-and-arbitrary-base-change` and `cor-cbc-derived-extension-zero-base-change` are etale results. `lem-sfb-abelian-open-extension-base-change` is an existing later non-blueprint node for general coefficient-category sheaves with the reverse comparison orientation; it is not used to move the item's argument wholesale to another node. No other imported blueprint node found by the proetale-extension-zero search states this same assertion. Therefore the item's `same_as` remains empty.

## Tool uses

The inherited accepted tool-use fields are left unchanged. Their five tools are still needed: `lem-weil-proetale-weakly-etale-localization` supplies the small-site and ring identifications; `prop-weil-pbc-proetale-constant-ring-map` supplies constant coefficient typing; `lem-weil-pbc-ringed-topoi-module-adjunction` supplies module adjunctions; `lem-weil-pbc-localize-ringed-site-morphism` supplies the ringed localization square and its linear direct-image comparison; `prop-weil-pbc-proetale-constant-exact` supplies exactness of arbitrary scheme inverse image. These are generic tools for the blueprint's own right-adjoint argument, rather than replacements of its route. No extra tool-use acceptance is requested.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own states and proofs; no new statement-only tasks were needed.

## Review by Q50

I read the current main-20261015 item statement, both paragraphs of its proof, and its containing unit, alongside the repository chapter/unit records. I read the statements of every cited DAG node. I checked the corresponding local Stacks source passages: proetale.tex section-morphism (09A5) and definition-extension-zero (09AE), sites-modules.tex lemma-adjoint-pullback-pushforward-modules (03D7) and lemma-localize-morphism-ringed-sites (04J0), categories.tex lemma-transformation-between-functors-and-adjoints (0B65) and lemma-compose-counits (0DV0), and derived.tex lemma-right-derived-exact-functor (015F). For the two localization/derived natural-transformation facts stronger than the bare Stacks wording, the proof cites the existing DAG statements, including their Mathlib-leaf universal-property clauses, rather than claiming those clauses are in Stacks.

Step 1 uses exactly the inverse-image construction, the constant-ring structure-map theorem and the module adjunction theorem. The first constructs the morphisms and tensor pullbacks; the second identifies their constant coefficient rings; the third explicitly states the module Hom bijection. The ring is finite and commutative as required, and g and g_U are arbitrary scheme maps. The tensor identification has its two inverse maps written out, rather than assuming inverse image means tensor pullback without checking coefficients.

Step 2 uses the localization theorem's clauses (1)-(3) and the explicit inverse-image indexing category. Those statements give the site equivalence, restriction of coefficients, sheaf condition and colimit formula actually used. For an arbitrary open e, projecting phi gives the unique arrow from (T,T to W times_Z T); this proves terminality after taking the opposite category and the restriction formula. Applying it to j and j' checks both identifications at once. Naturality on T_1 to T_2 and the scalar action are stated. This is an elementary substitution into the cited definitions, not a new localization theorem.

Step 3 uses only the extension-by-zero node, whose statement explicitly gives exactness, degreewise action and the adjunction for finite commutative coefficients. Both j and j' are open by the square's hypothesis. No stalk-conservativity claim is used from this node; a geometric stalk prescription alone would not prove this base-change statement on the pro-etale site.

Step 4 uses the open-square definition, including its chosen projection-compatible fibre-product isomorphism. The forward and reverse maps and their compatibility with every arrow V_1 to V_2 follow by the fibre-product universal property with both projections displayed. This is elementary, and introduces no hypothesis on g or quasi-compactness assumption on j.

Step 5 uses the ringed localization theorem and the inverse-image definition. I checked the former's actual statement includes the direct-image comparison with the restricted R(T)-module action, rather than merely a definition of localized sites. The latter supplies the small universes, continuous finite-limit-preserving base-change functor and constant-section description of the coefficient map. Steps 2 and 4 identify the localized sites and functor with those for g_U; agreement on constant sections verifies the localized ring map. Thus every hypothesis of the ringed theorem holds, and its component is M(a_V) in the correct contravariant direction.

Step 6 uses the composite-adjunction definition and the conjugate-isomorphism unit-equation theorem. The latter explicitly gives a unique natural isomorphism for delta:R_2 to R_1, so it applies to delta=t inverse. I checked the types of the beta and gamma formulas and the units: eta_2 lands in R_2 L_2 and delta lands in R_1 L_2. The transposition therefore yields beta:L_1 to L_2, exactly the statement's direction. The inverse formula uses t and the other adjunction. The formulas make the asserted canonical map and its inverse explicit.

Step 7 is the degreewise chain-map calculation, with its two differential/naturality equations and two identity composites written out. It uses only the result of step 6. No boundedness or constructibility is assumed.

Step 8 uses the finite-constant inverse-image exactness theorem, extension-by-zero exactness, the exact-functor derived-factorization theorem and localization universal property clause (2). I checked that the exactness theorem allows an arbitrary scheme map and finite commutative coefficients, and that the two Mathlib-leaf nodes cover unbounded complexes and descent of natural transformations, respectively. Their actual statements say those things. Since beta and gamma are already inverse chain maps, preservation of composition and identities in the stated universal property gives inverse derived maps. There is no derived Hom calculation involving an underived g_*.

I checked delivery-errors B-E point by point: no new node can be hollow, elementary, duplicate, a relabelled clause or an unsearched Mathlib fact because none is introduced; the item remains self-contained through its existing statement dependencies; its mathematical statement is unchanged; every non-elementary ingredient is a cited statement, not a hidden use of a node's proof; quotations are verbatim; the proof uses no SGA route. Hypotheses are preserved on each application. Small cases tested were U empty (both sides zero), j the identity (the same inverse-image functor on both sides), g the identity (the same extension functor), X' empty, the zero coefficient ring and the zero/unbounded complex. The formulas remain defined and give the expected identities in all cases. No source or statement dispute remains.

## Validation

The required server dry run exited successfully (exit 0), printing `OK (not pushed)` at `249191800e`: server preflight passed, including the DAG and split checks. All 15 citation quotes were also checked against the current shared statements. No statement or maintainer-owned metadata changed. A final dry run follows the report-only citation-count correction before pushing.
