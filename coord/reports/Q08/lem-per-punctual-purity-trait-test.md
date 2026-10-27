## Worker report

Repaired returned item `lem-per-punctual-purity-trait-test` in `dag/nodes/sec-deligne-laumon-a1/`. The item is split with five assembly steps. Its statement, statement dependencies, source, blueprint provenance and all previously recorded searches remain unchanged. The retained report is saved separately as `report.before-route-repair.md`; previous queries and their results remain in `searches.jsonl` and in the item's search history.

Files written:
- `lem-per-punctual-purity-trait-test.json`: statement, split; no Mathlib match.
- `lem-per-trait-test-strict-completion-input.json`: statement only, unsplit; no Mathlib match. Supplies the regular strict completion and the one-way descent of its closed-point Kummer isomorphism.
- `lem-per-trait-test-prime-field-local-input.json`: statement only, unsplit; no Mathlib match. Supplies closed-point purity for an arbitrary regular local prime-field algebra, with no finite-type or excellence assumption.
- `lem-per-trait-test-mixed-regular-pair-models.json`: statement only, unsplit; no Mathlib match. Supplies marked simultaneous regular-pair models over a complete strictly henselian mixed-characteristic trait.
- `lem-per-trait-test-supported-kummer-continuity.json`: statement only, unsplit; no Mathlib match. Supplies a derived comparison square for the actual global supported Kummer arrow, including compatibility with the limiting class.
- `citations.json`: a verbatim statement quotation for every citation in each of the five assembly steps.

There are **4 new nodes and 0 Mathlib leaves**. None of the four new nodes contains a proof, proof dependency, Lean attachment or approved tool-use record. They are future stage-1 obligations, not newly certified purity theorems.

Attachments: none. I repeated the project-source search for the exact blueprint id and for punctual purity, strict completion, Cohen approximation and Gysin limits. The punctual-purity hits in `lean/WeilConjectures/` concern weights of Frobenius eigenvalues, not this cohomological purity assertion. No project declaration states this item or the new inputs exactly.

WANTED: none for stating this one-level split. The available ILO exposition supplies the completion and prime-field propositions and the trait reduction. The exact simultaneous approximation and derived supported continuity formulations are explicitly agent-formulated obligations; their source fields do not misrepresent them as verbatim ILO theorems. Their proofs are deliberately not claimed here.

## Repair of the return

The return is substantive. I read `coord/repair-notes/lem-per-punctual-purity-trait-test.json`, `coord/changes/20261024-Q84-gabber-purity-inputs.md`, and the exclusions in `coord/route-pivot-dropped.txt`. Q84 re-admits the finite-purity interface but preserves every unlisted exclusion and forbids transitive still-excluded inputs. The initial retained dry run passed at 4210eb5b040; that mechanical success did not resolve the route fault.

The five offending proof citations are all removed: `lem-per-punctual-strict-completion-test`, `lem-per-prime-field-punctual-purity`, `lem-per-complete-mixed-regular-pair-approximation`, `lem-per-transverse-gysin-limit`, and `lem-per-regular-lci-geometric-calculus`. The first four are replaced with the fresh statement-only obligations requested by the return, with fresh searches. Their withdrawn proofs are neither copied nor cited. In particular no new node cites `lem-per-ind-etale-closed-support-base-change`. The fifth citation is unnecessary: compatible length-d regular equations already witness the constant codimension function d in the live definition `def-per-regular-closed-immersion-codimension`; the approximation now states this witness explicitly.

I removed `split_report.tool_uses` as required by the minor C8 return, and wrote no top-level `tool_uses`. Generic off-unit uses are explained below for the maintainer to judge. The item and every new node's full statement/proof dependency closure were traversed against the current exclusion list: 10,450 reached nodes, zero still-excluded nodes at this checkpoint. Blueprint `via` records remain historical provenance, as the repair order requires; they are not active theorem dependencies. The statement of the item needed no correction and is not disputed.

## Sources and searches

I read the stage-1 brief, stage-1 contract, worker role, GOAL.md, SETUP.md's three levels, and delivery-errors B--E in both copies. I read the chapter and unit JSON records and the current latest blueprint proof `sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`. `blueprint_refs.py ancestor` gives `lem-per-artin-gabber-affine-curve`; the new inputs make precise its Step 3 regular finite-torsion purity input without changing the unit or chapter route.

For the item I read ILO Expose XVI Definitions 3.2.1--3.2.2 and Proposition 3.2.3 (printed pp.243--244), Propositions 3.2.4 and 3.2.5 (pp.244--245), and the opening paragraph of 3.7 (p.254). For strict completion I checked the paragraph after Definition 3.2.1, which states strict-henselization invariance, and Proposition 3.2.4, which states completion invariance for strictly henselian regular local schemes. The new node only asserts the descent direction needed here and records the regularity/dimension witnesses it supplies. It does not assert that the completion map of an arbitrary nonexcellent regular local ring is regular.

For the prime-field input I read Proposition 3.2.5, which applies to every regular prime-field scheme, with no finite-type assumption. The new local-ring form is sufficient both for the equal-characteristic complete ring and pointwise for the characteristic-p closed models. It is explicitly independent of the former node's proof graph.

For the mixed-characteristic models I read ILO I Theorem 2.9, printed p.9 (Cohen presentation), I Theorem 10.3(i), p.17 (Popescu for a regular ring morphism), and IV Theorem 4.1.8, pp.56--57 (Cohen ring lifting), against the reduction in XVI 3.7. Those ingredients alone do not state the simultaneous model theorem verbatim. The full regular-pair assertion, including regular quotients, preserved equations and both colimit identifications, is therefore a separate unsplit obligation. Ramified C to B is allowed and is not silently assumed smooth or regular.

For supported continuity I checked the supported Cartier Kummer construction of XVI 2.1, regular-sequence construction 2.3.1, and preserved-conormal base-change compatibility 2.2.3.1. I read Stacks Tag 03Q6 (`etale-cohomology.tex`, `lemma-directed-colimit-cohomology`) and searched the whole DAG for this tag and for supported Kummer continuity. Ambient/complement cohomology continuity alone does not state the desired compatible *derived arrow*: that extra comparison is the new obligation. Its formula is a commutative square in D(A), not a per-degree assertion offered as a derived identification.

Whole-DAG searches by source place, prime-field purity, completion, regular-pair approximation, Cohen, and supported Kummer continuity found the four excluded historical nodes and the other comparisons listed below. Blueprint searches for completion, prime field, Kummer, regular pair, strict henselization, punctual, 03Q6 and 09YQ found no blueprint node stating a new input. Existing completion/strict-henselization definitions define the constructions; they do not prove the cohomological-purity invariance statement.

For each of the four new nodes I ran two different LeanFinder phrasings, Loogle, grep and LeanSearch through `msearch.py`, and read the results saved in `<new-id>.search-results.json`. Every new `mathlib_searches` entry records the exact tool and query that ran and the complete returned output. All services answered. The local-algebra hits include henselianity of adic complete rings, local characteristic decompositions, and regular-sequence predicates; none states the approximation or canonical purity map. The affine-limit hits concern structure-sheaf sections or factorization of scheme morphisms, not etale supported Kummer classes. Kummer grep hits concern Kummer-Dedekind, field extensions and binomial valuations. The three Cohen grep hits are bibliography entries in Noetherian/OfPrime and ValuedCSP. No match was claimed. Previously logged item searches were read and reused rather than repeated.

## Review by Q08

I checked each step against the actual statements, not their proofs, and verified all twenty statement quotations in `citations.json` verbatim. The four new inputs are smaller mathematical ingredients of the reduction: none restates the implication from purity over traits to purity for arbitrary schemes. Each is independently quantified and has definitions for its notions, actual formulas, complete hypotheses, filled blueprint provenance, and no hidden proof in its statement. The exclusions and the minor C8 issue were the corrections, not merely a rebase of the returned delivery.

Step 1 uses the regular-scheme definition for the local ring at w. The new completion input explicitly supplies a complete strictly henselian Noetherian regular local B, the unchanged dimension, separably closed residue field and invertible ell, and the direction descending its canonical map to R. The regular-local-domain statement is exactly the domain fact used for the characteristic split. Positive ring characteristic of a domain is prime; residue characteristic zero makes all nonzero integers units in a local ring. The prime-field input then applies to B in each equal-characteristic case. If B is mixed characteristic, its residue prime differs from ell because ell is a unit. Nothing applies a general regular-morphism theorem to a nonexcellent completion map.

Step 2 uses the definition of regular local ring to choose d maximal-ideal generators and `lem-weil-pbc-regular-local-generators-regular-sequence` for the regular sequence. A zero-dimensional regular local ring is a field, which rules out mixed characteristic and justifies d at least one. The new approximation statement has exactly these hypotheses and explicitly supplies every later model hypothesis: small nonempty directed set, affine maps, regular integral finite-type flat ambient models, regular Noetherian characteristic-p quotients, preserved regular equations, quasi-projectivity, a complete strictly henselian mixed-characteristic base with ell invertible, and both colimit rings. The actual algebraic construction remains the separately queued obligation.

Step 3 applies the assumed test only to those ambient models, all satisfying its hypotheses. `lem-weil-pbc-finite-type-over-noetherian` applies because the trait is Noetherian; the quotient is explicitly Noetherian in the approximation statement. At every point of Z_a the regular local ring contains F_p, so the new *local* prime-field result applies; `def-per-punctual-purity` translates these local maps into punctual purity of Z_a. This pointwise application corrects the old direct citation of a global prime-field theorem. The length-d equations give codimension d by the regular-closed-immersion definition, without the excluded lci calculus. The precise (b)+(c) implies (a) clause of `lem-per-punctual-purity-two-of-three` supplies the canonical Kummer map, with both regular Noetherian schemes and invertible ell checked.

Step 4 uses `def-per-closed-support-plus-adjunction` and `lem-amb-closed-support-hom` for the identification of derived sections of the class with the supported global map. The latter explicitly states the ordinary derived-Hom/cone formula, not a pro-etale variant. The new continuity statement applies with c=d: both stage and limit pairs are affine regular Noetherian, and the explicit compatible equations satisfy its nonflat transition hypothesis. Its derived square identifies the same Kummer arrow, including its sign, and explicitly gives preservation of its isomorphism. Thus no uncited comparison of Gysin classes is hidden in the step. `lem-exc-etale-sheaves-gsets-point` gives the sheaves/Galois-sets equivalence; at a separably closed field its group is trivial. Taking module objects gives an exact conservative equivalence with A-modules, so sections detect all cohomology maps. `lem-weil-pbc-unbounded-derived-iso-cohomology` is precisely the isomorphism criterion, applied after the canonical fully faithful D+ inclusion already fixed by the definitions. This detection is only at the separably closed point, never on a general positive-dimensional scheme.

Step 5 returns through the one-way descent implication established in Step 1 and quantifies over all w by the punctual-purity definition. It does not assume the converse completion implication. Empty W is vacuous. All five proof steps are below 2,000 characters; none hides a longer inline lemma.

Small cases were checked for each new statement. Completion in dimension zero is a separable field extension followed by a trivial completion, and its Kummer map has codimension zero; no new obstruction is asserted. The prime-field input includes arbitrary fields and d=0. For d=1 complete traits, the model requirement includes the constant trait pair with its residue field; ramification does not force a smooth Cohen map. Higher-dimensional mixed characteristic retains its explicit marked regular parameters. For continuity, a constant diagram gives the identity comparison, c=0 gives ordinary etale continuity and the restriction class, and empty closed support gives the zero supported object on both sides. No flatness of transition maps is inferred. Negative cohomological degrees are governed by the derived square, and twists and the 2c shift are identical at all stages. No hypothesis of perfection, global finite dimension, finite type or excellence is added to W.

The off-unit generic tools are `lem-sc-regular-local-domain` (domain property), `lem-weil-pbc-regular-local-generators-regular-sequence` (parameters), `lem-weil-pbc-finite-type-over-noetherian` (Noetherianity), `lem-amb-closed-support-hom` (ordinary derived support), `lem-exc-etale-sheaves-gsets-point` (field topos), and `lem-weil-pbc-unbounded-derived-iso-cohomology` (derived isomorphism detection). Their statements are independent of this unit's Fourier/perverse route and do not replace it. The maintainer, not this worker, judges/records any tool-use approval. No SGA source, old excluded ind-etale input, or discarded proof graph is used.

## Not duplicates

The four new ids are the new statement-only obligations explicitly requested by the return. Historical excluded records are not usable substitutes and are not re-admitted by this delivery. In particular:

lem-per-trait-test-strict-completion-input vs lem-per-punctual-strict-completion-test: new one-way closed-point descent obligation, without the excluded node's proof or any ind-etale closed-support dependency; the old statement gives an equivalence and is still excluded.
lem-per-trait-test-prime-field-local-input vs lem-per-prime-field-punctual-purity: new local-ring closed-point obligation rather than the excluded global scheme theorem; no copy of its withdrawn proof.
lem-per-trait-test-mixed-regular-pair-models vs lem-per-complete-mixed-regular-pair-approximation: freshly queued algebraic marked-pair obligation with quotient ring and colimit data and explicit codimension witness; the previous split is excluded and its proof is not restored.
lem-per-trait-test-supported-kummer-continuity vs lem-per-transverse-gysin-limit: new derived-arrow comparison for regular affine pairs and twist c; the excluded theorem asserts per-degree supported and ordinary cohomology continuity for general Noetherian pairs and all twists, with a withdrawn proof.

The following source-tag overlaps do not supply the new derived arrow comparison. Each existing statement was read; none identifies the canonical supported Kummer arrow across preserved regular sequences without a flatness hypothesis:

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-etale-cohomology-class-descent: asserts ordinary etale cohomology continuity/descent; it does not state the supported derived-arrow square or compatibility of the limiting Kummer class.

lem-per-trait-test-supported-kummer-continuity vs lemma-weil-pbc-etale-cohomology-continuity: asserts ordinary etale cohomology continuity/descent; it does not state the supported derived-arrow square or compatibility of the limiting Kummer class.

lem-per-trait-test-supported-kummer-continuity vs lem-per-regular-immersion-class-calculus: gives the supported class, composition and flat/local/strict-local compatibility, but not the derived supported comparison across this general nonflat affine limit.

lem-per-trait-test-supported-kummer-continuity vs det-sf-comparison-affine-continuity: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs sk-prop-sf-comparison: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs sk-thm-pe-direct-image-comparison: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs affine-open-inverse-image-unit-representatives: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs affine-open-sections-canonical-colimit-core: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs affine-open-sections-canonical-transformation: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs affine-open-sections-descent: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs affine-open-sections-zero-detection: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-affine-open-inverse-image-compatible-refinement-compatibility: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-affine-open-inverse-image-compatible-refinement-data: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-affine-open-inverse-image-compatible-refinement: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-affine-open-inverse-image-finite-local-lifts: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-affine-open-representing-cover-descent: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-etale-class-vanishing-spreads: spreads ordinary cohomology vanishing from a local scheme to an open neighbourhood; no supported class or derived-arrow comparison is stated.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-etale-cohomology-limit-of-schemes: asserts ordinary etale cohomology continuity/descent; it does not state the supported derived-arrow square or compatibility of the limiting Kummer class.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-etale-cohomology-local-ring-colimit: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-etale-restricted-cohomology-neighbourhood-colimit: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-gabber-principal-class-locally-zero: concerns vanishing or etale/Zariski comparison under strictly henselian hypotheses; it does not supply the supported Kummer continuity square for general regular affine pairs.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-gabber-strict-henselian-zariski-comparison: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-integral-cover-kills-constant-cohomology: kills an ordinary cohomology class after a finite cover; it does not give continuity of the derived supported Kummer map.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-strict-henselian-cohomology-locally-zero: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-strict-henselian-stalk-sections-comparison: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs lem-weil-pbc-strict-henselian-stalk-sections-epi: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-affine-vanishing: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-canonical-colimit: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-cocone-colimit: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-comparison-map: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-descent-equality: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-local-stalk-sections-descent-sections: concerns sections, descent or refinements of affine open neighbourhood diagrams, with no regular pair, supported Kummer arrow or derived-arrow continuity assertion.

lem-per-trait-test-supported-kummer-continuity vs new-strict-henselian-stalk-sections-comparison-iso: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs lem-sfb-proetale-derived-evaluation-continuity: concerns etale/pro-etale comparison or derived evaluation; it does not identify the specified closed-supported Kummer maps along arbitrary preserved-equation pairs.

lem-per-trait-test-supported-kummer-continuity vs lem-pur-classical-localization-triangle-transport: transports an ordinary etale localization triangle to the pro-etale finite-field setting, rather than comparing the supported Kummer arrow along affine limits.

## Validation

The retained pre-repair dry run exited successfully before any new invocation. After the mathematical repair, the required deliver.py --no-push exited successfully at e0a1a4a7b87 with server preflight passed; its DAG and split checks accepted the sandbox delivery. I then added the explicit abstract-derived-category reference for D(A) in the continuity statement and refreshed its verbatim citation. The final dry run checks that citation-only clarification before pushing. Only one deliver.py invocation is kept active at a time. No local checker, Lean compiler, Lake command, repository git command, launcher edit, or repository write was performed.
