# Worker report: lem-sfb-stable-labelled-isom-trait-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stable-labelled-isom-trait-extension.json`: statement, split; six proof steps using existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: one exact statement quotation for every step/node citation.
- `report.md`: this report and signed mathematical review.

Sandbox-only working records: `searches.jsonl`, `write_split.py`, and `citation-audit.md`. The latter records the first draft's full citation statements; the authoritative final step citations are `citations.json` and the node itself.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and stable/pointed/marked/labelled isomorphism terminology. The hits concern unrelated pointed etale schemes, Frobenius modules, or stability under isomorphism, not this theorem. No finished project declaration states all clauses. The item is therefore split, not attached. No Lean was written and no compiler or Lake command was run.

## WANTED

None needed for this assembly. The existing lattice node records a wanted pointed-curve reference of its own. I do not claim that Stacks 0E97 proves the marked, persistently nodal lattice comparison, and I do not silently treat the de Jong PDF, which is not present here, as read.

## What was wrong or incomplete

The item was statement-only. Its statement is correct and is unchanged. Its source already explicitly distinguishes it from Tag 0E97, whose local source I read: that lemma assumes a smooth proper unmarked generic curve and the proof follows minimal models and contractions. Consequently it cannot be applied to the arbitrary nodal generic fibre allowed here. The proof is marked agent-written and assembles the existing stronger logarithmic lattice and reconstruction statements instead.

The stable-pointed definition uses projective-bundle projectivity, whereas reconstruction and lattice comparison require finite-projective-space projectivity. Step 1 explicitly supplies this conversion after the trait pullback, using the affine projective-bundle presentations and the fact that an open in a local spectrum containing its closed point is the entire spectrum. No excellence, finite-type hypothesis on the trait, or genericity hypothesis on its map to S was added.

## Blueprint route and duplicate search

I read `dag/chapters/sec-six-functors-basics.json` and `dag/units/sk-thm-sf-ctf-stability.json`, the fixed three-level rules, and the parent `lem-sfb-stable-pointed-isom-finite`. This item carries the parent's DVR-existence/uniqueness input, hence the alteration/stable-model prerequisite of the direct-image argument. It does not replace a chapter or unit step. The ancestor tool reports `blueprint.from.node = None`; this is the existing imported chain's value and is retained, as is its explicit place and via list.

Whole-DAG searches for `0E97`, `unique-stable-model`, `pluricanonical`, `section-lattice`, and logarithmic reconstruction found the existing `lem-sfb-semistable-log-pluricanonical-lattices` and `lem-sfb-nodal-log-canonical-reconstruction`. Blueprint searches for `stable pointed`, `stable model`, and `pluricanonical` returned no blueprint match. I reused the existing nodes; no auxiliary node restates this item or a clause of it. `same_as` remains the searched empty list.

## Mathlib searches

The item's historical searches are preserved verbatim. New searches were actually run with the prescribed msearch command and appended from `searches.jsonl`, with exact tool/query text and actual metadata. Both semantic phrasings were read. LeanFinder returned valuative-criterion interfaces, Weierstrass minimal models and generic scheme morphisms; LeanSearch returned general cocone extension, completion, valuative uniqueness and scheme-property results. The Loogle combination of AlgebraicGeometry, Isom and Valuation returned zero hits. The AlgebraicGeometry grep for stable curves, pointed curves and pluricanonical terminology returned zero hits. None supplies the stable marked nodal extension theorem. There are no new nodes requiring separate search logs.

## Not duplicates

No new nodes were created. The two principal existing curve nodes supply different inputs: reconstruction applies to one positive log-canonical family, while lattice comparison concerns generic pullback of forms for arbitrary semistable families without stability. Neither states the trait-isomorphism conclusion; their combination does.

## Review by Q38

I read delivery-errors B through E in both copies, and reviewed each step against the full statements of all its cited nodes. The final citations JSON contains the verbatim full statement for every use, rather than a paraphrase substituted for a missing clause.

For the item I read Stacks `moduli-curves.tex`, `lemma-unique-stable-model` (0E97), including its proof. I also read `lemma-gorenstein-dualizing` (0E6R) and `lemma-stable` (0E74), and `morphisms.tex`, `lemma-characterize-relatively-ample` (01VJ), `lemma-proper-ample-is-proj` (0C6J), and the proof of `lemma-projective-over-quasi-projective-is-H-projective` (087S). These motivate the actual existing marked inputs; their unmarked formulations are not substituted for the marked statements. There are no new-node sources to review.

Step 1 uses the stable-pointed definition's actual bundle embedding, flat finite presentation and geometric component conditions. I checked that the affine-presentation node states a closed embedding of each bundle restriction into finite projective space, not merely relative ampleness. Closed-immersion base change supplies its pullback; the projective-space fibre-product definition identifies the ambient pullback. Composing the two closed immersions is a two-line affine quotient calculation, and factorization through an open containing the closed point of the local spectrum is elementary. The two permanence nodes explicitly give flat and finite-presentation base change for arbitrary maps. The semistable-marked base-change statement explicitly says that the relative smooth locus pulls back; I added that citation in self-review instead of taking relative smoothness solely from geometric fibre identification. Every geometric fibre over the trait is the identical original geometric fibre at the composite geometric point into S, so component stability, connectedness and reducedness impose no field or generic-point restriction.

Step 2 uses the DVR definition's explicit Noetherian equivalence, not excellence. The reconstruction node explicitly gives canonical dualizing modules, the section-divisor twist, the degree formula, ampleness from positivity, and reconstruction by the full graded section algebra. The degree check is written for all three cases g=0, g=1, and g>=2. It applies even when n=0 or the generic curve is nodal.

Step 3 uses precisely the injectivity, equality of section-lattice images, and multiplication/unit compatibility in `lem-sfb-semistable-log-pluricanonical-lattices`. I checked its hypotheses against step 1: the family is H-projective over a DVR, flat finitely presented, with connected reduced nodal geometric fibres and disjoint smooth marks. This node does not assume stability, excellence, or smooth generic fibre. Its statement gives the canonical generic pullback, so the algebra comparison is the one prescribed by u_K, not an arbitrary comparison or a rescaling by a power of the uniformizer. The injective maps identify sections with their images, degree by degree, and the multiplication clause makes the assembled bijection an algebra isomorphism.

Step 4 uses Proj functoriality's graded-equivalence and flat-base-change clauses. Properness is supplied by the projective-implies-proper node, and its hypotheses were proved in step 1. I read `coherent.tex`, `lemma-flat-base-change-cohomology` (02KH), and checked the full existing `lem-pc-flat-base-change-cohom` statement: for i=0 it applies to the quasi-coherent invertible powers on these proper, hence qcqs, families and the flat map Spec K to Spec R. I added an explicit citation of the existing localization-flat node for flatness. Fractions show multiplication compatibility. The proper-ample reconstruction node explicitly gives the chart formula and isomorphism-naturality equation used here; it does not promise arbitrary nonflat base change of section modules. Only localization is used, so the generic reconstruction comparison follows from its actual chart formulas and flat base change. The order of the two Proj maps is checked: Phi goes from A_Y to A_X, so Proj(Phi) goes from Proj A_X to Proj A_Y, and the resulting map goes from X to Y.

Step 5 writes the elementary reducedness/density argument needed by step 6. Flatness makes multiplication by the uniformizer injective on the structure sheaf. Localization is the generic fibre; geometric reducedness implies reducedness by the injective map of a vector space into its scalar extension. Thus nilpotents vanish and every nonempty affine open meets D(pi). This remains true for persistently nodal total spaces, so I do not incorrectly assume normality or integrality of X. The proper-implies-separated implication is part of properness. This is marked elementary because the argument is given directly from the cited definitions and the properness result, with no concealed curve theorem.

Step 6 uses `lem-sfb-relative-separated-dominant-ext` twice, with all hypotheses explicit: first a reduced trait, dense generic point, and the separated target, to prove equality of section morphisms; then the reduced total curve and dense generic fibre, to prove uniqueness of the whole morphism. I read `schemes.tex`, `lemma-where-are-they-equal` (01KM), which constructs the closed equalizer, and checked that the existing node is the relative separated-target form rather than a lemma requiring absolute separatedness. The structural composites agree because all maps are over T.

Edge tests: a three-pointed projective line has positive log degree 1, while a two-pointed line is unstable and excluded; a one-pointed elliptic curve has degree 1; an unmarked stable component has positive degree by its node branches or genus. The empty marking contributes an empty collection of section equalities. Generic automorphisms are arbitrary: Phi is built from their actual canonical pullback, so the proof does not force the identity. Reducible and persistently nodal generic fibres are covered by the lattice input and the reduced, not integral, uniqueness argument. A constant map of the trait to a closed point of S causes no problem. A nonexcellent DVR still gives the Noetherian trait and flat fraction-field localization needed here.

No new statement, hollow definition, circular dependency, source-only proof step, forbidden SGA source, or hidden lemma inside a step over 2000 characters was introduced. All six steps are below that threshold. No foreign node was changed. Off-unit generic geometric tools are declared in `split_report.tool_uses`; the substantive marked-curve route is unchanged.

## Unfinished work

None for this one-level stage-1 split. Its existing prerequisites remain independently queued or reviewed according to their own states. The required server dry run and delivery are run after this report.
