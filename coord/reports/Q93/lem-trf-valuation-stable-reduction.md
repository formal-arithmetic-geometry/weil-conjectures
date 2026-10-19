# Q93: lem-trf-valuation-stable-reduction

## Files written

All paths are in this item's sandbox. The shared project and both upstream source trees were read only; no git, Lean, compiler, Lake, or local preflight/check_dag/review_split command was run there.

- dag/nodes/sec-trace-formula/lem-trf-valuation-stable-reduction.json: item, split into seven proof steps; original statement retained.
- dag/nodes/sec-trace-formula/lem-trf-valuation-strict-semistable-local-uniformization.json: statement, unsplit, no Mathlib match. Finite local models along centred valuations, not a global proper model.
- dag/nodes/sec-trace-formula/lem-trf-valuation-strict-semistable-cofinality.json: statement, unsplit, no Mathlib match. Domination of an arbitrary modification of an already strictly semistable unmarked curve.
- dag/nodes/sec-trace-formula/lem-trf-valuation-marking-semistable-separation.json: statement, unsplit, no Mathlib match. Resolve only the marking on an already strictly semistable curve.
- dag/nodes/sec-trace-formula/lem-trf-valuation-semistable-stable-contraction.json: statement, unsplit, no Mathlib match. Contract a GIVEN semistable modification to a stable one.
- dag/nodes/sec-trace-formula/lem-trf-birational-quasi-modification-common-cover.json: statement, unsplit, no Mathlib match. General finite-component birational refinement and open cover, with no semistability assertion.
- dag/nodes/sec-trace-formula/lem-trf-valuation-horizontal-curve-models.json: statement, unsplit, no Mathlib match. Finite presentation and pure dimensions of modified curve models and schematic closures of generic markings.
- citations.json: one verbatim statement quotation for every node used in every proof step.
- searches.jsonl: the msearch command's actual log. research/ contains its complete output per proposed node, the search plan and the scripts used to produce these sandbox files.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact item id, stable reduction, stable modification, finite height, semistability and quasi-modification. No project declaration states the item or any new input. The upstream master checkout was not used as evidence of a finished proof.

## Sources wanted

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, 14 April 2010, literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, especially Proposition 4.5.1 p. 33 and §§3.2, 3.5, 4.2--4.4, for this item and the six new nodes.

The named local PDF does not exist in the shared literature directory. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including pp. 15--17, 20--21 and 24--33. No source was written into the read-only repository or downloaded to it. The item proof_origin is conservatively marked agent until archival promotion; each source record specifies the exact proposition/lemma and pages read. This is an archival request, not a claim that the PDF is already in literature/. No SGA source is used.

## What was wrong or missing

The item was an unsplit statement with no proof or proof dependencies. Its mathematical statement agrees with the smooth-generic existence portion of Proposition 4.5.1 and needs no repair. The important missing argument is how local valuation models become a SINGLE proper modification before applying stable contraction globally. Merely applying Proposition 4.3.3, or merely citing another copy of stable reduction, would not prove it.

The already existing Riemann--Zariski finite-refinement node is restricted to integral schemes of finite type over Z and a separable closure of their function fields. Neither hypothesis describes the present curve over V. I did not silently apply that node to X. The new birational refinement node supplies the arbitrary qcqs birational statement from Proposition 3.2.6 and the valuation description, including the cover consequence and the finite-component case.

Strict transform of the marking means its SCHEMATIC CLOSURE from the generic fibre; taking the full inverse image can introduce unwanted vertical subschemes. The model lemma states the required construction and finite presentation. Stability relative to the intermediate curve does not imply stability relative to X: Step 7 applies contraction again after composition.

## Source error

The opening of Temkin §4.2 says that a connected C has connected generic fibre by flatness. That inference, without an additional hypothesis, is false. For a nontrivial valuation domain V and nonzero nonunit t, take

C = Spec(V[x,z]/(x(x-t))).

It is finitely presented, free over V as a V[z]-module of rank two, hence flat, and has pure relative dimension one. It is connected: the two irreducible components Spec(V[z]) meet over t=0. Its generic fibre is the disjoint union of two affine lines, hence smooth and disconnected. This example also works when Frac(V) is separably closed and V has finite height. Consequently I do not identify connected total spaces with integral ones. The statement of Proposition 4.3.3 is used for the finitely many generic components; the general refinement is formulated componentwise with reduced component closures and their finite disjoint union. This corrects a reduction in the source's exposition and does not change the item's assertion or unit route. No claim of a false imported item is made.

## Searches and prior work

There was no item node, report, proof or searches.jsonl in the sandbox at entry, only dispatcher brief markers. Thus there was no prior split to preserve or dry-run first. I copied the current item metadata and retained all its prior Mathlib searches and blueprint ancestry.

For each of the six proposed nodes and for the item I ran two different LeanFinder phrasings, LeanSearch, Loogle and grep through the prescribed msearch.py command: 35 searches in all. All services returned actual results. Their exact queries, returned signatures and grep locations were read; each node records the same query strings and honest no-match verdicts. Weierstrass minimal models/good reduction concern a different object and cannot give these general nonproper marked-curve assertions. Etale/flat base change, standard-smooth charts and rational-map representatives do not give nodal models, modification cofinality, a common proper refinement, marking separation, or exceptional contraction. The horizontal-model grep does find Mathlib/RingTheory/Flat/TorsionFree.lean, including flatness/torsion-free results; these alone do not give finite presentation, pure fibre dimensions and the geometric closure assertions, so this is not a one-line Mathlib specialization. There are zero Mathlib leaves.

Before creating nodes I searched the whole DAG by source propositions and concepts, the Lean project by notions and tags, and tools/blueprint_refs.py by stable modification, uniformization, semistable, quasi-modification, blow, horizontal and Riemann. The broader blueprint hits for blowups, horizontal pasting and Riemann--Roch do not state any new theorem. The nearest blueprint ancestor is lem-trf-local-term-locality. Every new from.node and via list was obtained from that ancestry and its place identifies both the semistable-alteration branch and the precise Temkin input. All same_as fields are empty after those searches.

## Not duplicates

lem-trf-birational-quasi-modification-common-cover vs lem-trf-riemann-zariski-finite-refinement: the existing node assumes an integral finite-type Z-scheme and a separable closure, and concludes generically finite refinements; the new node treats arbitrary reduced qcqs schemes with finitely many generic components, and birational quasi-modifications in their own function fields. Its application to the non-Noetherian valuation curve is not a special case of that finite-type node.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-valuation-stable-reduction: centred valuation lifts to finite local strictly semistable quasi-models, without a global proper map or marking, rather than global stable reduction.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-valuation-stable-reduction: starts with an already strict unmarked model and a specified proper modification, and produces a dominating strict model; it does not construct a stable model for an arbitrary curve.

lem-trf-valuation-marking-semistable-separation vs lem-trf-valuation-stable-reduction: the underlying curve is already strictly semistable; only the generic marking is separated from other markings and nodes. This is Lemma 4.3.2, not the whole stable reduction existence assertion.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-valuation-stable-reduction: requires a given semistable proper modification and factors that map by contractions. Constructing such a modification is precisely the remaining argument carried by the item's steps; the new lemma cannot be applied to the original input before that construction.

lem-trf-valuation-horizontal-curve-models vs lem-trf-valuation-stable-reduction: records flatness, finite presentation, fibre dimensions and generic marking closures of already specified models; no semistability or stable existence is asserted.

lem-trf-valuation-horizontal-curve-models vs lem-trf-semistable-marked-base-change: construction of modified models and schematic closures is different from pullback of a given multipointed pair along a morphism of bases.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-stable-modification-uniqueness-normal: contraction gives existence from a supplied semistable model; uniqueness only compares stable modifications that already exist. The existing uniqueness node is reused in Step 5, so no duplicate restricted uniqueness node was created.

lem-trf-birational-quasi-modification-common-cover vs cor-nagata-blowup-product-common-refinement: the existing assertion is about two specified ideal blowups and their comparison morphisms, not compactifying arbitrary quasi-modifications into open pieces of one proper model.

The first dry run flagged the shared arXiv number 0707 as if it were a Stacks tag. I opened every listed existing statement (the finite-type model, dualizing degrees, base change, spreading, uniqueness, finite refinement, and the item) and checked their different conclusions and hypotheses. These are all inputs from different places of the same Temkin paper, not interchangeable statements. The complete pair comparisons follow.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-valuation-stable-reduction: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node asserts global stable-modification existence for an arbitrary smooth-generic marked curve.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-marked-curve-finite-type-model: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-marked-nodal-dualizing-degrees: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-semistable-marked-base-change: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node pulls back a supplied pair along a base morphism and does not construct or contract curve modifications.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-stable-modification-spreading: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-birational-quasi-modification-common-cover vs lem-trf-stable-modification-uniqueness-normal: the new node constructs a common proper birational refinement of a finite valuation cover of an arbitrary reduced qcqs scheme; the existing node compares stable models that already exist and has no existence, refinement, marking-resolution or contraction assertion.

lem-trf-valuation-horizontal-curve-models vs lem-trf-marked-curve-finite-type-model: the new node constructs flat finitely presented models and schematic closures on already specified valuation-curve modifications; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-valuation-horizontal-curve-models vs lem-trf-marked-nodal-dualizing-degrees: the new node constructs flat finitely presented models and schematic closures on already specified valuation-curve modifications; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-valuation-horizontal-curve-models vs lem-trf-riemann-zariski-finite-refinement: the new node constructs flat finitely presented models and schematic closures on already specified valuation-curve modifications; the existing node assumes a finite-type Z-base and a separable closure, unlike these arbitrary valuation-curve or birational constructions.

lem-trf-valuation-horizontal-curve-models vs lem-trf-stable-modification-spreading: the new node constructs flat finitely presented models and schematic closures on already specified valuation-curve modifications; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-valuation-horizontal-curve-models vs lem-trf-stable-modification-uniqueness-normal: the new node constructs flat finitely presented models and schematic closures on already specified valuation-curve modifications; the existing node compares stable models that already exist and has no existence, refinement, marking-resolution or contraction assertion.

lem-trf-valuation-marking-semistable-separation vs lem-trf-marked-curve-finite-type-model: the new node separates the marking on an already strictly semistable valuation curve; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-valuation-marking-semistable-separation vs lem-trf-marked-nodal-dualizing-degrees: the new node separates the marking on an already strictly semistable valuation curve; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-valuation-marking-semistable-separation vs lem-trf-riemann-zariski-finite-refinement: the new node separates the marking on an already strictly semistable valuation curve; the existing node assumes a finite-type Z-base and a separable closure, unlike these arbitrary valuation-curve or birational constructions.

lem-trf-valuation-marking-semistable-separation vs lem-trf-semistable-marked-base-change: the new node separates the marking on an already strictly semistable valuation curve; the existing node pulls back a supplied pair along a base morphism and does not construct or contract curve modifications.

lem-trf-valuation-marking-semistable-separation vs lem-trf-stable-modification-spreading: the new node separates the marking on an already strictly semistable valuation curve; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-valuation-marking-semistable-separation vs lem-trf-stable-modification-uniqueness-normal: the new node separates the marking on an already strictly semistable valuation curve; the existing node compares stable models that already exist and has no existence, refinement, marking-resolution or contraction assertion.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-marked-curve-finite-type-model: the new node factors a supplied semistable modification by contractions, which cannot supply the initial semistable model; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-marked-nodal-dualizing-degrees: the new node factors a supplied semistable modification by contractions, which cannot supply the initial semistable model; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-riemann-zariski-finite-refinement: the new node factors a supplied semistable modification by contractions, which cannot supply the initial semistable model; the existing node assumes a finite-type Z-base and a separable closure, unlike these arbitrary valuation-curve or birational constructions.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-semistable-marked-base-change: the new node factors a supplied semistable modification by contractions, which cannot supply the initial semistable model; the existing node pulls back a supplied pair along a base morphism and does not construct or contract curve modifications.

lem-trf-valuation-semistable-stable-contraction vs lem-trf-stable-modification-spreading: the new node factors a supplied semistable modification by contractions, which cannot supply the initial semistable model; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-marked-curve-finite-type-model: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-marked-nodal-dualizing-degrees: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-riemann-zariski-finite-refinement: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node assumes a finite-type Z-base and a separable closure, unlike these arbitrary valuation-curve or birational constructions.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-semistable-marked-base-change: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node pulls back a supplied pair along a base morphism and does not construct or contract curve modifications.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-stable-modification-spreading: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-valuation-strict-semistable-cofinality vs lem-trf-stable-modification-uniqueness-normal: the new node dominates a specified modification of an already strictly semistable curve by another strict model; the existing node compares stable models that already exist and has no existence, refinement, marking-resolution or contraction assertion.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-marked-curve-finite-type-model: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node descends an input pair to a finite-type Z-base and asserts none of these local model constructions.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-marked-nodal-dualizing-degrees: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node computes a line bundle and degrees on a supplied stable model over a Noetherian base.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-riemann-zariski-finite-refinement: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node assumes a finite-type Z-base and a separable closure, unlike these arbitrary valuation-curve or birational constructions.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-semistable-marked-base-change: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node pulls back a supplied pair along a base morphism and does not construct or contract curve modifications.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-stable-modification-spreading: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node spreads a stable valuation model that has already been supplied to a quasi-model of a finite-type base.

lem-trf-valuation-strict-semistable-local-uniformization vs lem-trf-stable-modification-uniqueness-normal: the new node supplies only local strict quasi-models covering centred valuations, with no global proper stable model; the existing node compares stable models that already exist and has no existence, refinement, marking-resolution or contraction assertion.

## Review by Q93

I read the worker brief, stage-1 contract, SETUP three levels, GOAL, dag-sync, chapter and sk-i-curve-zero unit, and delivery-errors B--E in full. This is below the existing Temkin input of the unit's semistable alteration branch; no chapter/unit record, target or maintainer-owned binding was changed.

For the item I read Proposition 4.5.1, p. 33. For local uniformization I read Proposition 4.3.3, pp. 29--30; it is a finite valuation-cover assertion, not a proper semistable modification. For strict cofinality I read Proposition 4.3.1, pp. 27--29, and retained its specified domination while forgetting blowup structure. For marking separation I read Lemma 4.3.2, p. 29: the underlying curve is already strict, the generic marking is etale, and the conclusion removes marking collisions and intersections with nodes. For contraction I read Proposition 4.4.6, pp. 32--33, including the successive blowdown factorization; a semistable model is a necessary supplied input. For refinement I read Proposition 3.2.6 and Corollaries 3.2.5/3.2.7, pp. 16--17; the finite-component extension is by component closures and finite disjoint union. For horizontal models I read Remark 4.1, the §4.2 opening and Lemma 3.5.1, pp. 20 and 24--26: over a valuation ring the torsion-free closure rings are flat and finite-type flat algebras are finitely presented. That last point is substantive and has not been hidden in an elementary step.

Step 1 uses exactly the model lemma's reducedness/finiteness conclusions and the local-uniformization node's finite centred-valuation cover. The assumptions are the item's unchanged finite-height separably closed valuation field and smooth generic curve. The empty curve is handled before applying a function-field argument.

Step 2 uses the new refinement node's actual conclusion of ONE proper modification with covering open pieces which modify the local models. Its hypotheses are checked: X is reduced with finitely many components by Step 1, and finitely presented over affine T, hence qcqs. The model lemma supplies the flat finitely presented marked pair (X_1,D_1), generic isomorphism and closure restrictions; these properties are not taken from a definition node. Every local Y_i has a smooth generic open by the explicit local-uniformization statement.

Step 3 uses strict cofinality with Y_i, not with an arbitrary unresolved curve. It uses the model lemma to put the prescribed closure marking on the dominating Z_i. Then marking separation has all of its hypotheses: Z_i is strict and the generic curve/marking are smooth/etale. Proper permanence (a) justifies both pair composites. I corrected the density explanation to intersect dense isomorphism opens and test injectivity on the reduced generic fibre; I do not assume an unproved isomorphism-neighbourhood containing the whole generic fibre.

Step 4 uses the contraction node only AFTER Step 3 has supplied its semistable modification. Proper permanence (b) justifies restriction to the target overlap; the model lemma says the marking closures restrict correctly. The short component argument establishes preservation of stability under open restriction of the target: every contracted rational component over a target point lies in its full inverse image, so its special points do not change. This is an elementary restriction check, not a separate lemma.

Step 5 reuses the existing normal-base uniqueness statement, opened and read in full. It asserts exactly unique isomorphisms of stable eta-modifications for normal integral qcqs T with smooth generic curve and etale generic marking. I checked those hypotheses for each overlap, including the elementary valuation-ring integral-closedness argument and the empty overlap case. Its actual uniqueness clause yields the triple cocycle. I did not use the invalid direction 'models are isomorphic, hence chosen isomorphisms are automatically a cocycle', nor rely on a proof internal to the cited node.

Step 6 uses the existing scheme-gluing statement, opened and read, once for curves and once for markings, after establishing its exact overlap and cocycle hypotheses. The remaining operations are explicit local verifications: glue compatible continuous/sheaf maps and ideals; check flatness, finite presentation, relative dimension and nodality on the finite open covers; check the properness definition locally after all base changes. Stability is checked on the entire contracted component over a target point. Thus no unnamed existence/descent theorem for stable models is hidden here.

Step 7 uses proper permanence (a) for the global pair composite and the supplied semistable-to-stable contraction again, now over the original X. I specifically checked that stability relative to X_1 was not confused with stability relative to X. No field extension, discreteness, excellence, Noetherian assumption, properness or separatedness over T has entered.

The item statement and all six new statements were tested at height zero (generic fibre is the whole base, so the identity models satisfy the assertions), empty marking, an already strict curve, already stable modification, a single affine smooth curve, disconnected generic components, and a nontrivially valued field with a non-finitely-generated maximal ideal. I checked that nothing assumes the markings finite or proper over T. The new nodes have statements only; proof and proof_deps are empty. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these files. All notions have definition citations or inline meanings; quotations in citations.json are literal parts of the statements. No proof step is over 2000 characters (largest 1310), and none hides a separate comparison lemma. The only off-unit proof tools are generic scheme gluing and proper permanence, declared in split_report.tool_uses with their purposes.

## Unfinished work

No portion of this one-level split is intentionally left unfinished. The six statement-only inputs remain for later stage-1 workers by design. The PDF needs maintainer archival promotion. Server dry-run and final delivery outcomes are given by the required delivery command.
