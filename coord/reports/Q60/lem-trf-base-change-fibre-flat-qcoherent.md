## Worker report

Item: lem-trf-base-change-fibre-flat-qcoherent. Group Q60, stage 1, 2026-10-23.

Files written: dag/nodes/sec-trace-formula/lem-trf-base-change-fibre-flat-qcoherent.json (the item, split); citations.json (one verbatim statement quotation for each of ten step/node citations); this report. The sandbox initially had no item or report, so the live unsplit item was copied. No repository or launcher file was changed. No Lean was written or compiled.

New nodes: 0. New Mathlib leaves: 0. All ingredients were already present in the DAG.

Attachments: none for the item. The existing project instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback belongs to lem-weil-pbc-module-pullback-quasi-coherent; that existing attachment was reused without editing its node. It proves the quasi-coherence clause only. The project source has no declaration tagged with this item's id and no declaration found by the fibre/base-change/flat/quasi-coherent concept searches giving all its clauses. In particular, the geometric-fibre isomorphisms in WeilSheaf/BaseChangeField/Geometric.lean concern different geometric fibres and do not prove this package. Sheaf/AlgebraicGeometry/PointwiseFlatnessBaseChange.lean states a generic ingredient with sorry; it is not a completed attachment.

WANTED: none.

The item statement is unchanged and agrees with the first paragraph of Stacks 05DC. Its empty proof was replaced with five steps, and its proof dependencies are exactly the union of their uses. No statement dispute was found. The Stacks display writes X_{s'} where the base-changed fibre X'_{s'} is meant; the item's existing notation already disambiguates that. No SGA source is used.

## Existing-node and blueprint searches

Read GOAL.md, the stage-1 brief and stage document, the three blueprint levels in SETUP.md, the chapter sec-trace-formula, and unit sk-i-curve-zero. Read the current main-20261015 ancestor lem-trf-local-term-locality and its blueprint_update. This is an inherited generic commutative-algebraic input in its nearby-cycle/semistable-alteration branch, not a replacement of the unit's contraction argument.

Searched all DAG node statements/titles for fibre base change, pullback quasi-coherence, locally finite type and Noetherianity, and flat base change. Read the exact statements of lem-weil-pbc-fibre-of-base-change, lem-pc-field-extension-flat, lem-sfb-pointwise-flatness-base-change, lem-weil-pbc-lft-base-change, pqf-lem-locnoeth-lft, lem-weil-pbc-module-pullback-quasi-coherent, def-pc-module-pullback, def-weil-residue-field, def-weil-flat-morphism and pqf-def-locnoeth. All were reused. The finite-type-over-Noetherian node was considered but its finite-type hypothesis is stronger than what is available globally, so the locally finite type node pqf-lem-locnoeth-lft is used instead.

Ran tools/blueprint_refs.py ancestor and searches for 'fibre base change', 'fibre of base change', 'flat base change', 'quasi-coherent pullback', 'field extension', 'fibre', 'flat fibre', 'module-pullback', and 'locnoeth-lft'. The broad searches found related blueprint nodes, not another statement of this package. No new node is needed and the item's same_as remains empty. Existing from.place identifies the precise inherited 05DC paragraph and is retained.

## Mathlib searches

Preserved the original Q33 searches and read their recorded results. Ran fresh searches through msearch.py only, recorded verbatim from searches.jsonl in the item: LeanFinder for the whole fibre/flat/module assertion, Loogle with AlgebraicGeometry.Flat and AlgebraicGeometry.LocallyOfFiniteType, grep for fibre-flat and pullback-quasi-coherence patterns, LeanSearch for the package, and a second LeanFinder phrasing for the canonical iterated module-pullback isomorphism. All services answered. Hits include Flat.isStableUnderBaseChange, locallyOfFiniteType_isStableUnderBaseChange, Scheme.Hom.fiber, Scheme.Modules.pullbackComp and sheaf pullback composition. They are ingredients, not the complete item. The second phrasing confirms that composition is already supported and supplies no reason for a new node.

Read the exact existing Mathlib fibre-square declaration at AlgebraicGeometry/Fiber.lean:65, the local Noetherianity theorem at AlgebraicGeometry/Noetherian.lean:239, and module pullback composition at AlgebraicGeometry/Modules/Sheaf.lean:241. Read the project quasi-coherent pullback instance in WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Tilde.lean:406, including its proof, which has no sorry. No claim is made that a combination of these independent results is a one-line Mathlib leaf for the item.

## Review by Q60

I read divisors.tex, Tag 05DC (lemma-base-change-relative-assassin), its entire first proof paragraph and surrounding statement. It assumes locally finite type f and arbitrary quasi-coherent F, and asserts exactly the fibre field-extension square, flatness, pullback coefficients and local Noetherianity used here. I also read morphisms.tex Tag 01T6 (lemma-finite-type-noetherian), Tag 01U9 (lemma-base-change-flat), more-morphisms.tex Tag 047C (lemma-flat-locus-base-change), modules.tex Tag 01BG (lemma-pullback-quasi-coherent), and sheaves.tex Tags 0095-0097, especially lemma-push-pull-composition-modules. There are no new nodes whose sources need separate review.

Step 1 uses lem-weil-pbc-fibre-of-base-change. Its statement explicitly gives h, both projection equations and the cartesian square, with exactly r=g(r') and the induced residue field map. I use its statement, not its proof or a definition of fibre products in place of the theorem.

Step 2 uses def-weil-residue-field for the induced field homomorphism, lem-pc-field-extension-flat for the flat spectrum map, clause (1) of lem-sfb-pointwise-flatness-base-change, and def-weil-flat-morphism to pass from flatness at every point to flatness. The cartesian square is the one already established in step 1. The pointwise theorem is applied with the original morphism a:Spec(k') to Spec(k), and base map pi:Y to Spec(k), so its base-changed morphism is h, not pi'. Neither its finite-presentation clause nor its reflection clause is used; clause (1) assumes no Noetherianity or finite type. The off-unit theorem is declared as a generic tool in split_report.tool_uses, leaving the maintainer-owned tool_uses field untouched.

Step 3 uses lem-weil-pbc-lft-base-change on f to obtain locally finite type pi, pqf-def-locnoeth for the affine-cover criterion, and pqf-lem-locnoeth-lft with base Spec(k). The latter statement supplies precisely the local conclusion. The missing field-Noetherian observation is proved inline by classifying its ideals; it is not hidden in a definition citation. This avoids any quasi-compactness assumption on Y or Noetherianity assumption on S.

Step 4 uses lem-weil-pbc-module-pullback-quasi-coherent with morphism i and module F. Its statement says exactly that arbitrary scheme pullback preserves quasi-coherence. The existing completed Lean attachment was read as additional evidence, but the proof step cites the mathematical statement itself.

Step 5 uses def-pc-module-pullback: besides the tensor formula its statement explicitly includes the canonical composition isomorphism. The step applies that asserted isomorphism twice and the already-proved projection equation. It writes the entire chain (i')*(g')*F to (g'i')*F = (ih)*F to h*i*F with the first comparison inverted and the second forward. This is a routine two-comparison assembly, marked elementary. It does not invoke an unsupported base-change theorem for modules, identify inverse image with tensor pullback, or assume flatness of g. Canonical composition is independently supported by the ringed-space source Tag 0097 just read.

For C4 I opened every cited node and put its verbatim statement in citations.json; every required clause is actually in that statement. For C1 all non-elementary facts above are node citations; the ideal argument and composition of specified isomorphisms are written inline. B and D introduce no new nodes, so neither duplicates nor restatement nodes arise. All proof steps are below 2000 characters. The statement and retained metadata are unchanged, and no axiom or hollow definition was introduced.

I checked empty fibres (all pointwise assertions vacuous and the zero module comparison valid), identity g, the zero coefficient module, non-flat g (for example a closed point into an affine line), and an infinite disjoint union of finite-type k-schemes as Y. For the last case only local Noetherianity follows and that is all the statement claims. Infinite and inseparable residue field extensions remain flat and require no finite generation. The proof does not require S to be Noetherian or F coherent. The main correction during checking was to use the existing locally finite type local-Noetherian theorem instead of the stronger global finite-type theorem; no mathematical statement was changed.

Unfinished work: none in the split; server dry run and delivery results follow from the required delivery command.
