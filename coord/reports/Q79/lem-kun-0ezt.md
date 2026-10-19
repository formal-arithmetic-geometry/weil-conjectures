# Worker report: lem-kun-0ezt

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-0ezt.json`: seven-step repair of the returned split; statement and Lean record preserved verbatim from the current shared returned head.
- `dag/nodes/sec-smooth-purity/lem-kun-derived-exchange-cube.json`: new statement-only unsplit lemma for derived exchange around an arbitrary commutative scheme cube; not a Mathlib leaf.
- `dag/nodes/sec-smooth-purity/lem-kun-higher-exchange-coefficient-cube.json`: new statement-only unsplit lemma for degree-q exchange around a morphism of cartesian squares with any coefficient morphism; not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every citation of every item step.

Attachments: none. WANTED: none. Unfinished: the two new nodes join the stage-1 queue, as required; their proofs are not included in their statements or node proof fields. Relative continuity remains the existing `lem-kun-0eym`.

The earlier attempt and its actual logged searches have been preserved in `previous-report.md`, `previous-item.json`, and `searches.jsonl`. The original report incorrectly concluded that no extracted node was needed. This delivery corrects that conclusion, rather than merely dividing the long step into smaller paragraphs. It also restores the statement exactly: the interrupted attempt had changed its initial directed-index wording. No statement dispute is raised and no Lean record or source file is edited.

## Sources and searches

I read the current main-20261015 blueprint item, its `blueprint_update`, chapter and Kunneth unit records, and the retained and returned versions of the item. The blueprint's sole proof paragraph prescribes Stacks 0EZT through 0EYM; the repair keeps this route and the original first three proof steps and final colimit argument. The item is a supporting classical input, not the unit's key statement, so no unit record is changed.

I read Stacks `etale-cohomology.tex`, Tag 0EZT, `lemma-base-change-Rf-star-colim`, statement and full proof at lines 16410–16466, and Tag 0EYM, `lemma-relative-colimit-general`, statement and first proof paragraphs at lines 7567–7620. These paragraphs specify exchange followed by the coefficient map, both for transitions and for limit legs. I read `sites-cohomology.tex`, Tag 07A7, `remark-base-change`, and Tags 0E46/0E47, `remark-compose-base-change` and `remark-compose-base-change-horizontal`, around lines 4030–4120. The source omits the pasting verification; the extracted derived-cube node isolates the two-path coherence required here. The higher-coefficient node isolates the subsequent naturality and cohomology comparison, rather than assuming an unspecified isomorphism between the same objects. These are agent extractions of the implicit canonical-map comparison; no source claims they are separately numbered lemmas.

Before creating either id I searched the whole DAG for commutative/commuting cubes, morphisms of squares, exchange compatibility, and the source tags, and ran whole-blueprint searches for cube, commutative cube, exchange, naturality, 0EZT, and coefficient. The nearest blueprint ancestor is `lem-kun-0ezt`. Neither new id exists. In particular, the existing `lem-kun-bc-base-change` clause (2) concerns simultaneous base change of all four corners along one base morphism; its comparison faces are cartesian. Here transition and projection comparison faces need not be cartesian. Existing strict-henselization cube nodes impose strict-local geometric-point data. The abstract coefficient-exchange-mates node assumes an already displayed coherent pull-comparison cube and counit equations; it does not establish the canonical scheme inverse-image cube or its degree-q coefficient identification. These nodes cannot replace the extracted statements in one-line specializations. The vague cartesian-derived-image-map-exchange statement belongs to a fixed cartesian pullback diagram and one fixed coefficient sheaf, not arbitrary eight schemes and coefficients.

Project searches under slopmaster2 `WeilConjectures/` found no exact item tag or finished arbitrary cube declaration. `Etale.baseChange_naturality`, `BaseChangeTheorems/MorphismDefs.lean:258–264`, proves coefficient naturality for one fixed square; this supplies only part of the new comparison and is not an attachment. `Etale.higherDirectImage_limit`, `SmoothBaseChange/HigherDirectImage/Transition.lean:112–129`, fixes a base and coefficient and ends in sorry, so it cannot attach the item. The upstream master and existing stage-2 item signature are reference material, not finished proofs.

All historical item searches and their verdicts are retained. New searches were run only via msearch and are recorded verbatim in the new nodes, with results in `searches.jsonl`. Each proposed statement was searched with two different LeanFinder phrasings, Loogle, LeanSearch, and source grep. Services returned results in this pass. The derived searches return ordinary scheme pullback cocycles, module pullback composition, and general adjunction calculus. Loogle's `CategoryTheory.mateEquiv_vcomp` is the existing generic tool, not the scheme cube theorem including canonical inverse-image coherence; I read its actual source at `Mathlib/CategoryTheory/Adjunction/Mates.lean:157–182` and recorded the grep showing line 170. The degreewise searches return sheaf-of-modules pullback associativity, ring-theoretic etale base change, unrelated cohomology maps, and ordinary categorical square structure. None is the stated etale exchange map with a coefficient morphism. An abstract mates formula and a separate cohomology identification require an argument, so neither new node is marked Mathlib. Earlier unavailable/rejected or incorrectly scoped searches remain honestly labelled; none is invented or recast as a successful negative search.

## Review by Q79

The return has one required repair: the original fourth step hides non-elementary lemmas and must be replaced by short steps citing nodes for those arguments, while the statement and Lean record stay unchanged. I compared the current shared head with the retained attempt. I restored its exact statement and retained every maintainer-owned field, including its valid stage-2 Lean record, and kept the original first three steps. The derived cube equation is now the first new node; the passage through coefficient maps, degree-q cohomology, and the specified usual maps is now the second new node. The old fourth step is replaced by Steps 4–6 applying those nodes to transition and projection cubes. The concluding colimit argument is retained. No non-elementary step exceeds 2000 characters (the longest is the unchanged first step, 1235).

For Step 1 I opened `lem-weil-pbc-qcqs-morphism-permanence`: its clause (3) explicitly preserves both quasi-compactness and quasi-separatedness under arbitrary base change, so it applies to h_i. The limit square is proved cartesian by giving compatible stage lifts and using uniqueness of each lift; no unsupported interchange-of-limits theorem is invoked. The sheaf-level composition clause of `lem-weil-pbc-derived-inverse-image-composition` gives the displayed pullback comparisons and associativity; `lem-weil-pbc-inverse-image-preserves-colimits` states exactly the isomorphism induced by the coprojections. Thus the coefficient system on Y and its legs are the correct ones.

For Step 2 I read all of `lem-kun-0eym`, including its transition and leg specifications. Apply it with (V_i,B_i,u_i,A_i)=(T_i,S_i,g_i,F_i). Both transition families are affine and g_i is qcqs by the item hypotheses. Pulling back its canonical comparison along f, the cited inverse-image colimit theorem and composition comparison produce C_A with the asserted legs. For Step 3 use (Y_i,X_i,h_i,e_i^{-1}F_i); its qcqs hypothesis was proved in Step 1 and its two affine transition families are given. The coefficient colimit is exactly Step 1's one. The directed index is read in the source's usual small nonempty directed-set convention; I record that interpretation here without changing the already formalized statement. No absolute qcqs assumption, field base, properness, or cartesianness of transition faces is added.

For Step 4 I read the entire first new statement and checked its domains: square 0 is stage i and square 1 is stage j, with x,y,s,a the four inverse-system transitions. All six commutativity equations follow from the stage squares and the system. It gives exactly the derived equation in the step. For the second application square 1 is the limit and x,y,s,a are r_i,t_i,s_i,p_i; the cone equations supply its hypotheses. The node expressly permits noncartesian comparison faces. It names the inverse-image composition identifications and the target transport y^{-1}e_0^{-1} to e_1^{-1}a^{-1}, so this is not a citation to an unstated coherence fact.

For Step 5 I read the entire second new statement. Substitute F_0=F_i, F_1=F_j and phi=phi_ji. Its U and V explicitly include exchange followed by the appropriate coefficient morphism, so the transition formula of `lem-kun-0eym` is exactly what it supplies after pulling back along r_j and identifying r_i=x_ji r_j. Both geometric squares are cartesian by hypothesis, which is the additional hypothesis needed for the identification with the usual base-change maps. Only a morphism, not an isomorphism, is required of phi_ji. Therefore it gives d_j u_ji=v_ji d_i.

For Step 6 apply the same second node with square 1 the limit square, coefficients F_i and F, and phi the coprojection. Step 1 proves the needed cartesian limit-square hypothesis. The leg specifications in `lem-kun-0eym` identify U and V with lambda_i and mu_i; Step 1 identifies e^{-1} of the coprojection with the coefficient leg on Y. Thus the statement supplies beta lambda_i=mu_i d_i. The original cohomology and naturality argument has been extracted, not left as an inline assertion that the two calculations are the same.

For Step 7 I read `def-weil-pbc-category-colimit`: its universal property produces the map of colimits from d_i and a second map from d_i^{-1}. The transition identity of Step 5 proves compatibility of the inverses by multiplying by the two inverses. Their composites restrict to identities on every coprojection, hence are identities by uniqueness. The leg identity of Step 6 identifies beta with C_B d C_A^{-1}. This is elementary use of the cited universal property; no filtered-colimit exactness theorem is hidden here.

Both new nodes are self-contained statements with all eight schemes, all twelve arrows, and all commutativity assumptions introduced. Their notions have statement dependencies; their proof fields, proof dependencies and proof origins are empty/null because this delivery splits only the item. Their `created`, chapter, unit and blueprint ancestry fields are filled. The first is substantially smaller than continuity: it has no limits, index category, coefficients system, qcqs assumption, or isomorphism conclusion. The second is a finite-cube compatibility law with one coefficient morphism, not any clause of the item's limit-isomorphism conclusion. The new nodes are separate from their possible future proofs. Suggested route for their future proofs: compare the two inverse-image square composites using derived composition associativity, then take their mates using the existing mate-pasting theorem; for the higher-coefficient statement, postcompose by the coefficient map, use naturality, and apply the natural exact-functor cohomology comparisons and the existing cartesian base-change identification.

I checked small cases of each extracted statement: identity cube, identity squares, K=0, phi=0, phi=id, and q=0. In the zero coefficient-morphism case both sides of the second identity are zero; no cancellation of phi is used. On identity geometry it becomes the ordinary naturality equation for the given coefficient map. Empty schemes are permitted and introduce no missing nonemptiness assumption. Arbitrary noncartesian comparison faces in the first node are allowed because exchange is the commutative-square mate. In the second node only the two main squares are cartesian. The source does not require finite type, invertibility of torsion orders, smoothness or properness for either formal identity.

C1/C4: each item step now cites the exact statement supplying every non-elementary comparison. I generated citations.json from opened node statements and checked every quotation is literally present and every used id is included. No step cites a narrower cartesian-only result for a transition face. No proof of another node is treated as its statement. The inherited cross-unit tool declarations are retained only for actual direct proof citations; no maintainer `tool_uses` is changed. The new nodes inherit this unit and do not replace the blueprint route.

The first required dry run completed successfully before repair at 3d446c4adc, but that mechanical success did not satisfy the human's extraction requirement. This report and the new nodes correct the substantive failure. Final validation and push are run after these changes. No Lean was written and no compiler, Lake, build, shared-project git command, or live launcher edit was run.

## Not duplicates

lem-kun-derived-exchange-cube vs def-pc-derived-base-change-map: the existing statement concerns Canonical derived base-change morphism; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sk-thm-pe-direct-image-comparison: the existing statement concerns Direct-image comparison; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs cor-weil-pbc-geometric-fiber-finite: the existing statement concerns Finite-coefficient geometric-fiber formula; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-adjunction-conjugate: the existing statement concerns Conjugate transformations of adjoint functors; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-adjunction-mate: the existing statement concerns Mate of a transformation under two adjunctions; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-ambient-ringed-exchange: the existing statement concerns Ambient ringed exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-derived-exchange: the existing statement concerns Derived exchange map; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-derived-square-iso: the existing statement concerns Square isomorphism on bounded below derived categories; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-four-arrows: the existing statement concerns Four finite-level arrows; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-weil-pbc-strict-tower-operations: the existing statement concerns Specified derived operations and mate on strict pro-etale module towers; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs det-properbasechange-modules: the existing statement concerns Étale proper base change for module coefficients; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-coefficient-exchange-mates: assumes an abstract pull-comparison cube and counit equations; the new statement identifies the canonical scheme-cube maps without those additional coherence assumptions.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-exchange-bounded-comparison: the existing statement concerns The bounded below exchange comparison equation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-exchange-module-termwise: the existing statement concerns K-injective representative of the module derived exchange mate; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-exchange-termwise: the existing statement concerns The termwise construction of the derived exchange morphism; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-exchange-unbounded-transport: the existing statement concerns Transport of the exchange equation to arbitrary K-injective representatives; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-inverse-image-composition: the existing statement concerns Composition isomorphisms of derived inverse images and their coherence; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-derived-square-iso-pasting: pasting of cartesian square isomorphisms; the new comparisons have arbitrary noncartesian comparison faces and compare two paths around a cube.

lem-kun-derived-exchange-cube vs lem-weil-pbc-direct-image-composition-coherence: the existing statement concerns Associativity and unit laws of the composition isomorphisms of direct images; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-etale-underived-exchange-restriction: the existing statement concerns Underived exchange along an etale morphism is the restriction identification; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-exchange-forget-coefficients: the existing statement concerns The derived exchange morphism commutes with forgetting the coefficient ring; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-exchange-identity-pasting: pastes cartesian faces in a rectangle; the comparison faces here need not be cartesian and there are two paths around an eight-scheme cube.

lem-kun-derived-exchange-cube vs lem-weil-pbc-finite-level-rectangle: the existing statement concerns Finite-level exchange rectangle; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-frobenius-exchange-restriction: the existing statement concerns Finite-level exchange is the restricted ambient exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-mate-pasting: abstract adjunction pasting for supplied natural transformations; the new statement establishes the canonical scheme-cube comparisons or their degreewise coefficient consequence.

lem-kun-derived-exchange-cube vs lem-weil-pbc-mate-whisker: the existing statement concerns Mates are natural in the non-adjoint sides of the square; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: the existing statement concerns Canonical coefficient comparisons intertwine derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-module-abelian-stalk-exchange: the existing statement concerns Forgetting module coefficients in the stalk of derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-module-abelian-underived-exchange: the existing statement concerns Coefficient forgetting respects underived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement concerns Projection-formula coherence for a square of ringed topoi; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-square-iso-pasting: sheaf-level pasting of square isomorphisms, rather than derived exchange around an arbitrary cube or its degreewise coefficient identity.

lem-kun-derived-exchange-cube vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the existing statement concerns Strict tower exchange agrees with the canonical mate; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-weil-pbc-three-step-adjunction-comparison: assumes invertible pushforward comparisons; no exchange or coefficient comparison is assumed invertible in the new statement.

lem-kun-derived-exchange-cube vs lemma-weil-pbc-frobenius-tower-compatibility: the existing statement concerns Frobenius compatibility with tower transitions; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing statement concerns Operator and base-change naturality of the formula; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lemma-weil-pbc-target-locality: the existing statement concerns Target locality; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs prop-weil-pbc-derived-inverse-image-adjunction: the existing statement concerns Derived adjunction of inverse and direct image on D^+; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sk-def-exchange: the existing statement concerns Derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sk-thm-properbasechange: the existing statement concerns Proper base change on classical pro-étale complexes; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-coef-cartesian-section-adjoint-mates: the existing statement concerns Adjoint mates on cartesian derived sections; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sf-kunneth-coherence: the existing statement concerns Coherence of the relative product; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs det-prop-p1-adjunction-rational-triangle: the existing statement concerns Triangle identities for the rational projective line; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sk-def-sf-exchanges: the existing statement concerns Exchange and projection transformations, typed; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-base-change-restrict-scalars-arrow: the existing statement concerns Étale base-change arrows commute with restriction of coefficients; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-base-change-restrict-scalars-comparison: the existing statement concerns Coefficient comparison isomorphisms for the base-change source and target; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-completed-operations-linear-natural-exchange: the existing statement concerns Linearity and naturality of completed pullback, direct image, and exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-integral-test-pushforward-arrow: the existing statement concerns Integral pushforward identifies the two test-base comparison arrows; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-restrict-scalars-derived-adjunction-identities: the existing statement concerns Canonical coefficient comparisons preserve the derived adjunction; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-restrict-scalars-derived-exchange: the existing statement concerns Canonical coefficient comparisons commute with derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sbc-restrict-scalars-pullback-square-comparison: the existing statement concerns Canonical coefficient comparisons preserve inverse-image square transport; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sc-cartesian-derived-image-map-exchange: fixed cartesian pullbacks and a fixed coefficient; the new statements allow arbitrary comparison faces and, in the degreewise version, a coefficient morphism.

lem-kun-derived-exchange-cube vs lem-sc-limit-derived-direct-image-exchange: the existing statement concerns From degreewise affine-limit exchange to derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sc-limit-higher-direct-image-exchange: the existing statement concerns A single higher-direct-image exchange passes to an affine inverse limit; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs nt-target-etale-smooth-ring: the existing statement concerns AlgebraicGeometry.Etale.isIso_baseChange_of_smooth_of_ring_order_invertible; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sbc-lem-base-change-composition: the existing statement concerns Base change for a composite square; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sbc-thm-adic-smooth-base-change: the existing statement concerns Adic smooth base change; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sbc-thm-bounded-derived-smooth-base-change: the existing statement concerns Bounded derived smooth base change; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs sk-thm-smooth-base-change: the existing statement concerns Smooth base change; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-cbc-finite-constant-coefficient-transport: the existing statement concerns Normalized finite scalar and etale-origin transport to constant coefficient modules; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-cbc-strict-constant-tower-operations: the existing statement concerns Strict constant-coefficient towers and normalized inverse/direct-image operations; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-cbc-strict-tower-open-extension: the existing statement concerns Normalized exact open extension on strict constant-coefficient towers; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-cbc-strict-tower-proper-open-arrows: the existing statement concerns Unit-normalized proper and open arrows on strict towers; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs def-kun-commutative-derived-exchange: defines exchange for one commutative face; the new statement asserts compatibility of several exchanges.

lem-kun-derived-exchange-cube vs fix-lem-exchanges: the existing statement concerns Exchange functoriality: naturality, identities, and pasting; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-amb-unbounded-compact-support-comparisons: the existing statement concerns Unbounded ordinary etale compact-support comparisons; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-amb-unbounded-proper-open-interchange: the existing statement concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-cbc-proper-open-interchange-coherence: the existing statement concerns Proper/open interchange and its base-change and composition equations; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-cbc-strict-tower-proper-open-calculus: the existing statement concerns Normalized proper/open calculus on strict pro-etale towers; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-fin-radicial-exchange-descent: the existing statement concerns Descending the exchange property through a universal homeomorphism; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-finrepair-modification-extension-zero: the existing statement concerns Extension by zero under a proper modification; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-fix-compact-support-coefficient-change: the existing statement concerns Change of finite coefficients for compact support; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0eym: relative continuity constructs an isomorphism for a varying-base inverse system; the new statement compares exchange across a finite cube, not a colimit.

lem-kun-derived-exchange-cube vs lem-kun-0ezt: the item concludes an isomorphism at an inverse limit; the new statement is only a finite-cube canonical-map identity and has no continuity or isomorphism conclusion.

lem-kun-derived-exchange-cube vs lem-kun-0f09: the existing statement concerns Smooth base change for limits of smooth schemes; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0f1c-exchange: the existing statement concerns Field-extension exchange morphism isomorphism; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0f1h-sep-reduction: the existing statement concerns Reduction to a separably closed ground field; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0f1h: the existing statement concerns Base change for open immersions; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0f1i-normal: the existing statement concerns The normal integral case; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-0f1j: the existing statement concerns Base change for pushforward tensored with a bounded-below complex of finite tor amplitude; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-bc-base-change: simultaneous cartesian base change of all four corners along one base morphism; arbitrary transition/projection comparison faces here need only commute.

lem-kun-derived-exchange-cube vs lem-kun-bc-map-on-cohomology: the existing statement concerns Cohomology of a derived base-change map; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-commutative-exchange-chart: compares one exchange with cohomology pullback on an etale chart; the new statement compares exchanges on an eight-scheme cube.

lem-kun-derived-exchange-cube vs lem-kun-proj-formula-natural: the existing statement concerns Naturality of the projection formula; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-proper-base-change-torsion-ring: the existing statement concerns Unbounded proper base change over a torsion coefficient ring; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-unbounded-abelian-exchange-comparison: the existing statement concerns Unbounded coefficient forgetting identifies canonical etale exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-kun-unbounded-exchange-agrees: the existing statement concerns The unbounded exchange extends the bounded exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-pur-finite-universal-smooth-trace: the existing statement concerns The finite smooth trace is the scalar extension of the prime-power trace; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-pur-noetherian-etale-section-specialization: the existing statement concerns Normalized section specialization for ordinary etale dualizing complexes over a Noetherian base; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-sp-proper-open-tower-comparison: the existing statement concerns Open-adjunction normalization of proper/open interchange on strict coefficient towers; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs thm-asd-smooth-tensor: the existing statement concerns Smooth cohomological duality without a chosen orientation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs thm-cbc-complete-proetale: the existing statement concerns Complete pro-etale compact-support base change; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs thm-cbc-finite-torsion: the existing statement concerns Compact-support base change at finite coefficients; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-trf-compact-frobenius-transport-composition: the existing statement concerns Composition of compact-support transport along powers of geometric Frobenius; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-trf-finite-horizontal-shriek-mate: the existing statement concerns Compact-support exchange as a mate along finite horizontal arrows; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-derived-exchange-cube vs lem-trf-weil-shriek-iterates: the existing statement concerns Iterates of the Weil $!$-pushforward; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-coefficient-exchange-mates: assumes an abstract pull-comparison cube and counit equations; the new statement identifies the canonical scheme-cube maps without those additional coherence assumptions.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-derived-square-iso-pasting: pasting of cartesian square isomorphisms; the new comparisons have arbitrary noncartesian comparison faces and compare two paths around a cube.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-exchange-identity-pasting: pastes cartesian faces in a rectangle; the comparison faces here need not be cartesian and there are two paths around an eight-scheme cube.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-mate-pasting: abstract adjunction pasting for supplied natural transformations; the new statement establishes the canonical scheme-cube comparisons or their degreewise coefficient consequence.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-square-iso-pasting: sheaf-level pasting of square isomorphisms, rather than derived exchange around an arbitrary cube or its degreewise coefficient identity.

lem-kun-higher-exchange-coefficient-cube vs lem-weil-pbc-three-step-adjunction-comparison: assumes invertible pushforward comparisons; no exchange or coefficient comparison is assumed invertible in the new statement.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-chart-class-pullback-core: the existing statement concerns Canonical derived pullback of a class with pulled-back source; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-chart-restricted-raw-class: the existing statement concerns Specified raw class of the restricted chart cone map; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-derived-image-map: the existing statement concerns Cartesian derived image map; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-derived-image: the existing statement concerns Cartesian derived image; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-higher-image-chart-system: the existing statement concerns Cartesian higher image chart system construction; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-higher-image-leg: the existing statement concerns Cartesian higher-image leg; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-higher-image-limit: the existing statement concerns Cartesian higher-image limit; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-higher-image-stage: the existing statement concerns Cartesian higher-image stage; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-higher-image-transition: the existing statement concerns Cartesian higher-image transition; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-cartesian-image-projection: the existing statement concerns Cartesian pullback projection; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-sc-raw-restricted-cohomology-class: the existing statement concerns Canonical inverse-evaluation class and its pullback equations; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-abelian-derived-homology-sections: the existing statement concerns Abelian derived Homology sections comparison; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-class-pullback-zero: the existing statement concerns Pullback of the zero chart class; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-cohomology-evaluation: the existing statement concerns Evaluation of the canonical chart cohomology comparison; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-exchange-naturality: the existing statement concerns lem-sc-cartesian-chart-exchange-naturality; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-lift-naturality: the existing statement concerns Canonical chart cohomology lifts commute with stage transitions; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-raw-adjunction-pullback: the existing statement concerns Chart raw adjunction commutes with pullback and exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-chart-restricted-map-evaluation: the existing statement concerns Evaluation of the restricted chart cone map; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-derived-image-map-exchange: fixed cartesian pullbacks and a fixed coefficient; the new statements allow arbitrary comparison faces and, in the degreewise version, a coefficient morphism.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-affine-complex-presentation: the existing statement concerns Cartesian higher image affine complex presentation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-affine-section-local-vanishing: the existing statement concerns Local affine-cover vanishing of cartesian higher-image sections; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-affine-section-local-zero-sieve: the existing statement concerns Sieve form of local affine-cover vanishing; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-affine-section-vanishing: the existing statement concerns Eventual vanishing of affine cartesian higher-image sections; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-chart-comparison: the existing statement concerns Cartesian chart cohomology comparison; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-chart-system: the existing statement concerns Cartesian higher image chart system; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-finite-raw-class-vanishing: the existing statement concerns Common-stage vanishing of finitely many raw cartesian derived classes; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-germ-descent: the existing statement concerns Germ descent for cartesian higher images; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-germ-vanishing: the existing statement concerns Eventual vanishing of cartesian higher-image germs; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-raw-affine-descent: the existing statement concerns Cartesian higher image raw affine class descent; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-higher-image-stalk-colimit: the existing statement concerns Stalkwise filtered-colimit presentation of cartesian higher images; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-image-projection-fst: the existing statement concerns First projection equation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-image-projection-snd: the existing statement concerns Second projection equation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cartesian-raw-class-chart-representative: the existing statement concerns Finite-stage chart representative of a raw cartesian class; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-cofiltered-affine-etale-model: the existing statement concerns Cofiltered affine etale model; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-limit-derived-direct-image-exchange: the existing statement concerns From degreewise affine-limit exchange to derived exchange; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-limit-higher-direct-image-exchange: the existing statement concerns A single higher-direct-image exchange passes to an affine inverse limit; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-sc-restricted-over-abelian-cohomology-presentation: the existing statement concerns Restricted-over abelian cohomology presentation; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs stage3-cartesian-higher-image-single-raw-class-vanishing: the existing statement concerns Eventual vanishing of one raw cartesian derived class; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs def-kun-commutative-derived-exchange: defines exchange for one commutative face; the new statement asserts compatibility of several exchanges.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0eym: relative continuity constructs an isomorphism for a varying-base inverse system; the new statement compares exchange across a finite cube, not a colimit.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0ezt: the item concludes an isomorphism at an inverse limit; the new statement is only a finite-cube canonical-map identity and has no continuity or isomorphism conclusion.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0f09: the existing statement concerns Smooth base change for limits of smooth schemes; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0f1h: the existing statement concerns Base change for open immersions; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0f1i-normal: the existing statement concerns The normal integral case; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-0f1j: the existing statement concerns Base change for pushforward tensored with a bounded-below complex of finite tor amplitude; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-bc-base-change: simultaneous cartesian base change of all four corners along one base morphism; arbitrary transition/projection comparison faces here need only commute.

lem-kun-higher-exchange-coefficient-cube vs lem-kun-commutative-exchange-chart: compares one exchange with cohomology pullback on an etale chart; the new statement compares exchanges on an eight-scheme cube.

lem-kun-higher-exchange-coefficient-cube vs lem-pur-relative-support-coordinate-model: the existing statement concerns Geometric normal-slice comparison for supported cohomology; it does not state the general two-path exchange identity for arbitrary eight schemes and the specified coefficient maps.


## Continuation verification, 2026-10-17

The retained repair already contained the two extracted statement-only nodes and the logged searches. I read those results instead of repeating the unchanged questions. I compared it with the current shared returned head: the statement, Lean record and first three steps match exactly. I also restored the original final colimit step, changing only its references to the transition equation (now Step 5) and the leg equation (now Step 6). The final retained non-elementary step lengths are 1235, 726, 468, 644, 629 and 656 characters.

The first dry run of this continuation exited with two diagnostics for the same fault: the item still had status unsplit, so review_split also rejected its status. I corrected the item to split. No mathematical diagnostic was reported. I rechecked all 13 step-citation pairs against their actual statement text; every quote is verbatim and the list covers exactly the uses lists.

I reread the complete Stacks 0EZT statement and proof, the transition/leg construction in 0EYM, and the mate definition and composition remarks 07A7/0E46/0E47. I opened each directly used existing node, and the extracted statements themselves: qcqs base-change permanence supplies exactly the h_i condition; inverse-image composition and colimit preservation specify the coefficient diagram and both continuity comparisons; 0EYM specifies precisely the transitions and coprojection legs used in Steps 5 and 6. Both cube statements type-check as arrows from the same pulled-back source to the same derived or higher-direct-image target. The degreewise node retains an arbitrary, possibly zero, coefficient morphism, so no unwarranted cancellation is required.

Current whole-DAG and blueprint searches still find no exact duplicate. In particular lem-weil-pbc-right-derived-plus-cube assumes a supplied underived commutative cube, while the extracted derived node identifies the canonical scheme-cube exchange maps. lem-weil-pbc-abelian-exchange-cube-comparisons fixes a sheaf pulled back from one corner and concludes only a geometric-stalk equation. Neither gives the arbitrary bounded-below-object derived statement or the higher-sheaf identity with arbitrary coefficient morphism by one-line specialization. The two lem-sc-limit exchange nodes fix a field base and a single coefficient and assert isomorphisms; neither is a cube-comparison identity. The item remains on the prescribed 0EZT/0EYM route.
