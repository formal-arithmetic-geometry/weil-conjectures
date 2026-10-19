# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-sections-finite-pushforward-modules.json`: repaired item, six steps, statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-module-derived-restriction-resolution.json`: one new statement-only lemma, `unsplit`; Mathlib searches find no exact match.
- `citations.json`: verbatim current statement quotations for all 25 step/node pairs.
- `searches.jsonl`: retained original logged searches and appended actual repair searches.
- `report.md`: retained the original source/attachment/search findings and replaced the incorrect mathematical review with the repair review below.

One new node; zero Mathlib leaves. No Lean source, compiler, Lake, build, direct git command, shared-project write, or launcher write was used.

## Attachments

None for this item or its new node. Searching the project source by the item tag and by finite pushforward/global sections found `AlgebraicGeometry.Etale.mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso`, `WeilConjectures/SixFunctors/Finite/GlobalSections.lean:44`. Its complete declaration constructs only the Leray isomorphism, not the item's restriction square. The finite-exactness and exchange declarations are ingredients only. The existing `AlgebraicGeometry.Etale.etaleKInjective_unit_leray` recorded on `lem-weil-pbc-kinjective-unit-leray` explicitly uses `AddCommGrpCat`, not arbitrary module coefficients. The pro-etale module analogue uses a different site and finite coefficients. Neither is an attachment of the new etale arbitrary-ring statement.

## WANTED

None. All source documents used are present under literature/.

## What was wrong and what changed

The returned head was `7f0399c7c6`. Its Step 4 invoked abelian-sheaf pullback and Leray-composition nodes for an equality in `D(Mod Lambda)`. Its assertion that these facts simply transport to module coefficients omitted exactly the derived compatibility needed. Furthermore equality after applying derived scalar forgetting would not by itself prove equality of module-derived morphisms: conservativity is an isomorphism criterion, not faithfulness. I do not assume the forgetful functor preserves module injectives or K-injectives.

I compared the retained sandbox with the current shared node, which is still unsplit with no proof. Its statement, created ancestry, chapter and unit agree with the sandbox. The prior item's valid exactness and injective-normalization arguments are retained and made more precise. The statement and its hypotheses are unchanged; there is no statement dispute. All earlier Mathlib searches are retained; their results remain available in the node and log.

The repaired proof uses module resolutions throughout. A new general lemma computes derived module restriction followed by an arbitrary coefficient map on bounded-below injective section complexes. It has no finite morphism, Cartesian square, finite-pushforward comparison, or base-change isomorphism conclusion. The item still proves its own compatibility: Steps 4-5 calculate the module mate on ordinary sections, and Step 6 applies the generic resolution formula twice and equates the resulting chain maps. This is a split, rather than moving a clause of the item into its child.

Removed proof citations: `lemma-weil-pbc-finite-exchange`, `lem-weil-pbc-derived-cohomology-pullback-laws`, `lem-weil-pbc-derived-leray-composition`, `lem-weil-pbc-exact-functor-derived-functor`, and `lem-weil-pbc-bounded-below-injectives-kinjective`. Their places are taken by actual module constructions and the general injective-representative, K-injective-Hom and right-derived-computation nodes. Finite exchange invertibility is unnecessary for the stated square.

## What could not be finished

The item is split by one level. Its new generic lemma is deliberately statement-only and remains for a subsequent stage-1 item.

## Review by N8

I read the worker and stage-1 contracts, delivery-errors B-E, the three blueprint levels in SETUP, GOAL and dag-sync, the chapter/unit records, and the current main-20261015 statement and proof of the blueprint ancestor `lem-trf-local-term-locality`. The existing ancestry points through the finite-surjective Cech-descent input; this repair changes no unit route. I read Stacks `etale-cohomology.tex`, Tag 03QP, `proposition-finite-higher-direct-image-zero`, and the finite-exchange Tag 0959, `lemma-finite-pushforward-commutes-with-base-change`. The latter is not used as a derived module coherence theorem. For the new lemma I read `sites-cohomology.tex`, Tag 08J6, `remark-before-Leray`, which explicitly works with modules on ringed topoi, and `cohomology.tex`, Tags 01F8/01F9/01FB (`lemma-functoriality`, `equation-functorial-derived`, `remark-explain-arrow`), which spell out the resolution arrow. I read `derived.tex`, Tags 015M and 070I. The new node states the constant-coefficient ringed-site total-derived formula, not a claim that Tags 015M/05T2 alone prove the item's square. Its statement has no proof sketch; the intended proof is the module-resolution computation of these sources.

For Step 1 I reopened the three cited statements. Finite direct image is exact on abelian sheaves; the module-direct-image node says its underlying functor is exactly that one; the module-forgetting node says it is faithful and preserves kernels/cokernels. Reflection of zero homology is written out, so this use of underived forgetting is justified without a derived compatibility claim. The updated blueprint version of finite exactness is more general and agrees with this specialization.

For Step 2 I checked the module inverse-image adjunction's exactness and its actual module unit/counit against `prop-weil-pbc-inverse-image-modules-exact`. The exact-left-adjoint theorem gives preservation of injectives by every direct image. Enough injectives and the general `lem-weil-pbc-dplus-injective-representative` supply the bounded-below injective models; its statement explicitly permits arbitrary abelian categories and module sheaves. `lem-weil-pbc-kinjective-hom-derived` supplies actual comparison chain maps and uniqueness up to homotopy. `lem-weil-pbc-right-derived-plus-injective` computes the derived functor on these representatives. The two global-section complexes are equal as Lambda-module complexes, which proves the normalization and naturality rather than merely its underlying abelian version.

For Step 3 I checked `lem-trf-finite-radicial-basechange`: its first sentence states preservation of finite morphisms themselves, without assuming radiciality. It therefore gives finiteness of p'. Exact g-inverse-image preserves the lower bound. The injective-representative and Hom-derived statements apply to the module category on Z', and p'_* preserves both injectives and quasi-isomorphisms by Steps 1-2. Thus J and p'_*J really compute the two lower-right objects and their Lambda-module comparison.

For Step 4 I reopened the entire statement of the underived inverse-image-composition node: clause (2) gives exactly the composition comparison and its unit equation. It is an abelian-sheaf statement, so I explicitly prove the underived module lift: naturality commutes with each constant scalar endomorphism; local constancy of sections of the constant ring sheaf upgrades this to module linearity; faithfulness reflects the unit equation. The module inverse-image node explicitly says its underlying unit and counit are those of abelian inverse image. Consequently the beta used later is a module morphism with precisely the given normalization. This is a few-line underived deduction, not a derived transport assertion. It is declared as a generic off-unit tool use.

For Step 5 I checked the formula on an arbitrary section, viewed as a map from the regular constant module. The transpose of beta after inverse image of s is `g^{-1}(epsilon_p) g^{-1}p^{-1}(s)`, equal by functoriality to the inverse image of the transpose of s. This gives the full section-map equation, not merely agreement on cohomology. Module linearity is inherited from Step 4 and the adjunction, so equality of these actual section maps is equality in Mod Lambda. Applying it in every degree of L commutes with differentials by naturality.

For Step 6 I checked both substitutions in the new lemma. Its source injective complex is p_*L for h and L for g; its target is p'_*J for h and J for g. All are bounded below and termwise injective. Its arbitrary map a is p'_*t composed with beta_L in the first application and t in the second; the lemma requires no isomorphism of a. Exactness of inverse/direct images makes beta_M correspond to beta_L under the source resolution. The two horizontal lambda maps are exactly the endpoint module-complex identities established in Steps 2-3. Step 5 and the identity of sections of p'_*t with sections of t then make the two chain maps identical. Thus the conclusion holds in D(Mod Lambda), without using equality in D(Ab), without an unstated forgetful-K-injective claim, and without beta invertibility.

I tested the item and the new node on empty source/target, the identity maps, a zero complex, a complex concentrated in one degree, and Lambda=Z/nZ. The last case is material: an injective Lambda-module sheaf need not be injective after forgetting to abelian sheaves, but the repaired proof never needs that assertion. The new node permits a=0 and arbitrary non-quasi-isomorphisms and then computes the corresponding zero or coefficient map correctly; identity u gives ordinary derived functoriality. No torsion, Noetherian, flatness-of-Lambda or finiteness-of-Lambda hypothesis has been inserted. All six proof steps are below 2000 characters; the non-elementary resolution-normalization comparison is isolated in the new node rather than hidden in a long step.

Against delivery-errors B-E: the new node introduces every object, has definition dependencies, proper TeX and explicit source labels/tags, blueprint ancestry and only an unsplit statement. Searches of the whole DAG, whole blueprint and Lean source preceded creation. I compared the near-duplicates below rather than using their proofs for stronger statements. Every non-elementary step input is in uses and has a literal statement quote in citations.json. The item retains the mate calculation, with no clause relabelled as a child. Its new dependency does not depend on the item and no cycle is introduced. Both coefficient categories, functor domains, resolution hypotheses and canonical-map directions are explicitly checked above. No SGA source is cited.

## Not duplicates

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-kinjective-unit-leray: the existing statement is about complexes of abelian etale sheaves and equality in the abelian derived category; the new node is about arbitrary constant-ring module sheaves and equality of module-derived morphisms. Forgetting coefficients alone does not identify these Hom sets.

lem-trf-module-derived-restriction-resolution vs lem-trf-proetale-unit-leray-chain-formula: the existing statement works on the small pro-etale site with a finite coefficient ring and its separately constructed module adjunction; the new statement uses the etale module adjunction for every commutative ring.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-derived-unit-classical-pullback-coherence: the existing statement and its derived-unit/Leray comparison are explicitly abelian-sheaf valued; the new node proves the total-derived module chain formula for arbitrary coefficient map a.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-classical-pullback-resolution-sections: the existing statement concerns sheaves in degree zero, classical nonnegative abelian cohomology, and its comparison to a resolution; the new statement is an equality in D(Mod Lambda) for arbitrary bounded-below injective complexes and arbitrary chain map a.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-ext-pullback-resolution-sections: the existing statement concerns Ext/cohomology of abelian sheaves in degree zero, not the total-derived module morphism on arbitrary complexes.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-derived-module-underlying-comparison: the existing node identifies underlying abelian cohomology groups and their restriction maps; it gives no equality of maps in D(Mod Lambda) and no module chain-representative formula.

lem-trf-module-derived-restriction-resolution vs lem-pe-left-module-derived-evaluation-forget: the existing node compares module-derived sections after forgetting with abelian-derived sections; it does not compute the module-derived arrow itself. The new node makes no coefficient-forgetting assertion.

lem-trf-derived-sections-finite-pushforward-modules vs lem-fd-finite-pushforward-cohomology: the existing node only treats torsion abelian sheaves in nonnegative cohomology and lacks the normalized module-derived restriction square.

lem-trf-derived-sections-finite-pushforward-modules vs lemma-weil-pbc-finite-direct-image-exact: the existing node supplies exactness, whereas the item also constructs the normalized module sections comparison and proves its mate square.

lem-trf-derived-sections-finite-pushforward-modules vs lemma-weil-pbc-finite-exchange: the existing node supplies exchange invertibility. This item's square needs only the specified mate and proves its compatibility with module-valued derived sections.

lem-trf-module-derived-restriction-resolution vs lem-trf-derived-sections-finite-pushforward-modules: the item asserts finite-pushforward exactness, its normalized derived-sections comparison and a Cartesian mate square. The child only computes restriction followed by any chain map for an arbitrary scheme morphism; Steps 4-6 still prove the square.

lem-trf-module-derived-restriction-resolution vs thm-sp-grothendieck: the existing node constructs the Grothendieck spectral sequence and its edges for a single object. It has no module inverse-image unit or total-derived restriction-chain formula.

lem-trf-module-derived-restriction-resolution vs lem-sc-grothendieck-bottom-resolution-comparison: the existing node computes a spectral-sequence bottom edge on nonnegative homology of a single object. The child computes a total-derived module restriction arrow on arbitrary bounded-below complexes.

lem-trf-module-derived-restriction-resolution vs lem-sc-resolution-derived-single-unit-augmentation: the existing node compares the single-object derived-functor unit with an augmentation to a resolution. It has neither a scheme inverse-image adjunction nor its global-section restriction formula.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-derived-leray-composition: the existing node concerns composition of abelian-sheaf Leray comparisons for two morphisms. It does not give the module unit/chain-map formula for one morphism.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-derived-unit-leray-comp: the existing node gives composition of abelian-sheaf unit-Leray maps for two morphisms; the new node computes one such module-derived arrow on chain models for arbitrary coefficient map a.

lem-trf-module-derived-restriction-resolution vs lem-weil-pbc-derived-unit-leray-id: the existing node states the identity law only for abelian derived unit-Leray maps. It does not compute module-derived restriction for arbitrary morphisms and target chain maps.

lem-trf-module-derived-restriction-resolution vs def-pc-canonical-resolution-derived-iso: the existing definition specifies the resolution comparison for the derived value on a single object. It does not state a unit-section restriction theorem for arbitrary bounded-below module complexes.

lem-trf-module-derived-restriction-resolution vs lem-pc-canonical-resolution-composite-unit-comparison: the existing node compares homology components of a Grothendieck composite unit for one resolved object. The new node gives a total-derived module arrow under a scheme inverse-image adjunction.

lem-trf-module-derived-restriction-resolution vs lem-pc-canonical-resolution-homology-comparison: the existing node compares homology of the single-object canonical resolution isomorphism. It gives no scheme restriction map or module-derived chain formula.

lem-trf-module-derived-restriction-resolution vs lem-pc-grothendieck-resolution-unit-comparison: the existing node asserts existence of a single-object resolution isomorphism with two specified homology equations. The new node asserts a module-derived restriction equation for any bounded-below injective complexes and any a.

lem-trf-module-derived-restriction-resolution vs lem-sbc-raw-affine-complex-system-map-coherence: the existing node gives diagram composition/cocone laws on homology of abelian etale complexes. It neither works in module-derived Hom sets nor identifies restriction with a module-linear chain map.

## Mathlib search assessment

I read every new logged search result. LeanFinder's two phrasings returned classical injective-resolution maps, right-derived-zero comparisons, and sheaf/free-module infrastructure. LeanSearch returned generic derived adjunction-unit formulas. I opened `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean` through its derived-unit factorization and read `Mathlib/CategoryTheory/Abelian/RightDerived.lean:72-105,263-292`. The classical results resolve single objects in nonnegative degrees; the generic derived-adjunction theorem still needs the section and module Leray comparison and does not state the new node in one-line specialization. Loogle for the quoted `rightDerivedFunctorPlusBaseChange` name and the first grep returned no hits. The second grep returned the actual classical zero-derived declarations, whose source I read. These are recorded exactly as run in the new node and searches.jsonl, with no unavailable service recorded as a no-match.
