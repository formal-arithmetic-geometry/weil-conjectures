# Q148 stage-1 report

Item: lem-sfb-nonaffine-closed-test-exchange-identification.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nonaffine-closed-test-exchange-identification.json: statement, split; Mathlib searches found no match. Ten proof steps, using only existing nodes. The statement and statement dependencies are unchanged.
- citations.json: one entry per step/node citation, quoting the actual statement with its hypotheses. Full statements are quoted to preserve the restrictions on each interface.
- report.md: this report. searches.jsonl is the search tool's unmodified log. split.py is sandbox-only preparation code, not part of the delivery.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the item's blueprint tag and for closed-site lift, closed tests, exchange/restriction and nonaffine terminology. ClosedSiteLift, ClosedSiteAdjunction and AffineClosedSiteFunctorProperties concern the site functors, not this derived exchange identification. The existing Sheaf/Paper/ClosedTestDerivedExchangeModel record has an affine-source hypothesis and sorried declarations; it is neither a completed project attachment nor the nonaffine statement.

## WANTED

None. All sources used are available locally.

## Problems found and corrected

The imported node had no proof. Its affine-source predecessor cannot be cited for the nonaffine conclusion. I used only the source-independent covering/evaluation paragraph of lem-sfb-closed-lifted-test-isomorphism-criterion, and carried out the general-source computation from the ordinary direct-image section formula, exact pullbacks, K-injectives and localized ringed sites. No affine intersections or finite affine Cech descent are used.

The proof is explicitly marked agent-written: Stacks 09BK and 09BL supply the closed-site calculation, and 0D6F supplies derived section localization, but the source does not state this exact internal-module, nonaffine, normalized-mate theorem. The source also cautions immediately before 09BK that exactness of closed pro-etale pushforward is not available. This proof uses preservation of K-injectives by a right adjoint to an exact inverse image instead.

The chapter is sec-six-functors-basics and the inherited unit id is sk-prop-sf-comp-coherence. The older unit record points into sec-smooth-purity; I also read the current main-20261015 unit and its refinement proof in sec-six-functors-basics. The proof serves the closed-complement calculation in refinement (2), along the recorded ancestor det-sf-comp-coherence-cocycle. No route or target statement was changed.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Searches of the whole DAG for 09BK, 09BL, 0D6F, closed lifted tests, weak contractibility, localized sections and derived adjunctions found the nodes cited in the proof. Whole imported-blueprint searches for closed immersion, closed tests, cohomology-of-open and derived localization found no exact duplicate of this nonaffine theorem. In particular lem-sfb-closed-test-derived-exchange-model restricts X to be affine; det-sf-open-closed-pullback-limits requires a quasi-compact open complement and does not identify this exchange; lem-sfb-unbounded-sections-localization is a general ringed-site tool, not a duplicate of the exchange theorem.

## Mathlib searches

Preserved the item's existing search history. Ran the required logged msearch.py queries with leanfinder, loogle, grep and leansearch, including two different semantic phrasings. Read all returned hits. LeanSearch returned Scheme.Modules.restrictAdjunction_unit_app_app and restrictAdjunction_counit_app_app (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:442,447), Zariski open-immersion module formulas, not closed pro-etale derived exchange. LeanFinder's broader phrasing returned SheafOfModules.sheafificationCompPullback (Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:118) and ordinary sheafification/adjunction compatibility; I read that source. The other phrasing returned affine-space and scheme-limit section results. Loogle returned zero hits. Grep returned IsClosedImmersion lift facts and unrelated closed/field-lift results, not the requested cohomological comparison. No service was unavailable. None states the item or gives a one-line specialization of it. Exact tool/query strings and actual hit names are recorded in the node and in searches.jsonl.

## Review by Q148

I read proetale.tex, lemma-closed-immersion-affines (09BK), its proof, and lemma-closed-immersion-affines-apply (09BL), especially (1)--(2) and their proof, plus sites-cohomology.tex, lemma-restrict-K-injective-to-open and lemma-unbounded-cohomology-of-open (0D6F). I read the current blueprint unit statement and refinement proof (2), as well as the existing affine closed-test node's statement and proof. There are no new nodes with separate sources to review. Every existing node cited in the proof was opened and its statement read, not inferred from its title.

Step 1 uses the covering, henselian-pair, exact-evaluation and conservativity assertions actually stated before the affine-source hypothesis in lem-sfb-closed-lifted-test-isomorphism-criterion. The closed-site functor properties give the quotient fibre square and specialization into V. I corrected an overly quick appeal to henselian terminology for IB lying in the Jacobson radical: the proof now observes directly that every maximal point is closed, hence belongs to V by that specialization assertion. Fibre-product associativity identifies T_0 without assuming T affine.

Step 2 uses the internal/section-module equivalence exactly for its preservation of underlying sheaves and sections. The module pushpull definition specifies the underlying direct image and the lifted adjunction; def-sfb-finite-lower-star supplies the section formula for arbitrary scheme maps. The condensed localization theorem supplies the actual coefficient transport and literal restriction on a site object; it assumes neither an affine scheme nor discrete coefficients. These interfaces justify applying the ordinary ringed-site lemmas to the internal-module setting.

Step 3 checks the particular closed-evaluation isomorphism, not just its existence. W is geometrically w-contractible by the test hypothesis; the source-affine evaluation theorem applies to this affine site object even though X is nonaffine. The basis comparison passes the epimorphism property to the identity object over W. The closed-site counit theorem's specialization hypothesis is provided by 09BK, and its invertible-counit conclusion is exactly the hypothesis of the specialization unit-comparison theorem. The closed inverse-image evaluation and unit-section definition specify naturality and the map itself. The module adjunction from step 2 supplies its underlying abelian unit; no scalar-extension flatness is assumed.

Step 4 cites the definition of K-injective-derived module pushforward and the right-adjoint preservation theorem, whose exact-left-adjoint hypothesis is the stipulated exactness of f^*. Section localization applies to T as an object of X's small pro-etale site, because it is the base change of W. It is not necessary that T be an affine scheme. Exact evaluation at V was established in step 1. The first comparison is therefore the canonical section complex I(T), not an unrelated abstract isomorphism.

Step 5 repeats the K-injective calculation for h^*I and f_Z. The localized ringed-site morphism theorem identifies the pullback of the site object T with T_0, and its stated pullback comparison gives (h^*K)|T_0 = b^*(K|T). This is an actual cited comparison, rather than an implicit identification of coefficients or objects.

Step 6 explicitly expands the unit, square and counit for the ordinary mate. The ambient exchange definition gives that exact formula; the finite-upper-star definition gives the sheafified Kan-extension description; the module pushpull definition gives the lifted adjunction; and the inverse-image-unit-section definition specifies the restriction of a section. Evaluating the counit on the representative indexed by W returns its evaluation on X times_U W. Cancellation is the adjunction triangle identity. This proves the particular map, without borrowing the affine node's conclusion.

Step 7 uses the derived-adjunction theorem's stated normalization of the derived counit. With J a K-injective resolution of h^*I, the transpose is h^*epsilon followed by j, so uniqueness of adjunction transpose gives exactly the specified derived exchange. Exact evaluation preserves this chain-map calculation.

Step 8 uses the explicit K-injective localized-restriction theorem for both I and J; I added this citation during the C4 audit rather than using the proof of the section-localization node. The right-adjoint preservation theorem applies to b_*, since b^* is exact. The composition theorem therefore applies to b_* followed by sections. The right-derived universal-property node normalizes its identity-on-sections comparison, and the derived slice-localization theorem expressly states compatibility with units and counits. This computes the restriction defined in the item's statement, with no claim of its invertibility.

Step 9 uses the K-injective Hom theorem for both representative independence and morphisms. Naturality of the actual unit section and of the closed-evaluation comparison gives test-object naturality on the same complexes. Shifts are termwise and preserve the displayed formulas, including their signs. For the connecting square I cite lem-sfb-ambient-qcqs-exchange-canonical-shifts, which states precisely compatibility of the ambient exchange with shifts and all arrows of a distinguished triangle, with no finiteness hypotheses. It does not presuppose that exchange is invertible.

Step 10 uses the underived and derived localized-ringed-site comparisons, whose statements supply the identity section formula and compatibility with adjunctions. Applied at the affine open in the larger target, they identify all the complexes and unit maps already constructed, which is the required compatibility. This claim is about open restriction, not arbitrary closed base change.

I tested I=0, I=A, A the zero ring, the zero module/zero complex, empty tests, and the zero coefficient ring. The maps respectively reduce to identities or to the unique maps of zero complexes. For a genuinely nonaffine source, such as a projective line over U, T is a legitimate site object and the same section calculation applies; nowhere is its higher cohomology declared zero. Tests are required to be w-contractible, not the schemes T and T_0. No properness, finite presentation, Noetherian hypothesis, finite coefficient assumption or exactness of closed direct image enters. Every proof step is shorter than 2000 characters. The generic off-unit tools are declared in split_report.tool_uses for review, rather than inserted as already-approved top-level tool uses.

## Unfinished work

None for the stage-1 split. Existing cited unsplit nodes remain their own stage-1 items; this delivery does not purport to finish their proofs. Server preflight and delivery results are recorded below when run.
