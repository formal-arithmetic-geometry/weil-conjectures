## Worker report

Files written: `dag/nodes/sec-deligne-laumon-general/lem-zl-immersion-higher-shriek-base-change.json` (item, statement unchanged, now split), `citations.json`, and this report. The command-generated `searches.jsonl` is retained. No Lean or repository file was written and no compiler was run.

## New nodes

None. Zero Mathlib leaves. All required facts already have DAG nodes. The natural cohomology composite and its specialization to a heart object are proof steps, not additional lemmas.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag found nothing. The relevant `WeilSheaf/LowerShriekPackage.lean:148` declaration `AlgebraicGeometry.WeilComplex.nonempty_upperStarDerivedLowerShriekIso_of_isPullback` gives only existence of a derived isomorphism, rather than all of this item's heart-valued, canonical-map and naturality assertions. `WeilSheaf/ProperBaseChange.lean:95` is sorried; its higher-cohomology consequence concerns proper ordinary direct images, not the item. No attachment is claimed.

## WANTED

None. The item follows the available current blueprint. No SGA source is used.

## Audit and changes

The item was an unsplit node with no proof. Its complete statement, statement dependencies, source and blueprint provenance are retained. The proof now writes the actual composite of the inverse immersion cohomology comparison and cohomology of the canonical derived exchange, then identifies the degree-zero specialization. The source is `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-excision/lem-zl-morphism-open-closed-reduction.proof.md`, Part 2: the displayed compact-support base-change isomorphisms and the Sheaf form sentence about exact pullbacks. The ancestor's more general complex version is obtained by the same functorial operation. The chapter and unit route is unchanged.

The original Mathlib search records are preserved. Six additional searches were run through the prescribed Q36 msearch command, exactly as recorded in searches.jsonl and appended to the item: LeanFinder with two formulations, Loogle, LeanSearch and grep with two patterns. The semantic hits give scheme restriction/composition or ring-module scalar base change. I read Mathlib's `AlgebraicGeometry/Modules/Sheaf.lean:390-465`, including `restrictFunctorIsoPullback`, which concerns structure-sheaf modules on the Zariski site, not constructible adic Weil coefficients. The other hits include ordinary sheaf inverse-image adjunctions and composition; they do not supply compact-support direct images. Neither grep nor Loogle found the compact-support Weil operations. No match was declared.

DAG and whole-blueprint searches covered base change, higher compact support, cohomology pullback, t-exactness and immersions. The existing general `prop-functor-package` gives the derived isomorphism; it is not the heart-valued higher-image statement of this item. `lem-zl-immersion-weil-local-behavior` gives the exact immersion cohomology comparison. No new node duplicates either. All proof dependencies were read, and a read-only dependency traversal found no path from them back to this item. Every proof step is shorter than 2000 characters.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The item is a cohomological consequence of existing derived exchange, not a newly introduced restatement of it.

## Review by Q36

I read the current Part 2 source with the item's complete statement open, then read the statements of all six proof dependencies. I also read the current `prop-functor-package` proof and `fix-prop-coherence` statement and proof in `sec-six-functors/sk-thm-sf-package/`. The available source itself explicitly invokes the arbitrary compact-support clause of the package; it does not impose properness on f or smoothness on the immersion. No source correction or statement dispute was needed.

Step 1 takes the derived compact-support exchange from clause (4) of `prop-functor-package`, not its separate proper/smooth ordinary-image clause. I checked the common-stage Qbar coefficient domain and the separated finite-type assumptions on the four corners. This is exactly the item’s coefficient category, with no conversion to discrete nontorsion étale coefficients. `fix-lem-exchanges` clause (1) states that the transformations are natural and identifies compact-support exchange with the completed and field-transported maps. `fix-prop-coherence` explicitly states field-coefficient Weil equivariance. Thus the proof uses a specified natural Weil exchange rather than choosing an arbitrary isomorphism. These are generic operation tools from the six-functor package, explicitly used by the ancestor proof; their off-unit uses are declared in split_report for the maintainer to judge.

Step 2 uses the package's bounded constructible domain to put L=Rf!K in the domain of clause (1) of `lem-zl-immersion-weil-local-behavior`. That node states the natural Weil isomorphism H^r(h*L) ≅ h*H^r(L), for every integer r and every locally closed immersion under exactly the finite-field/common-stage hypotheses here. Its statement, not its proof, supplies that comparison. This avoids incorrectly using `prop-constructible-truncations` alone for arbitrary immersion t-exactness: that proposition's pullback clause is only about automorphisms.

Step 3 uses `prop-constructible-truncations` for the actual heart-valued cohomology functor. The remaining reasoning is elementary functoriality: the inverse of H^r(B) composed with the comparison is explicitly written, and the two inverse identities follow from preservation of composition. Naturality and commutation with the Weil isomorphisms follow by composing the already commuting squares from steps 1 and 2. No derived category of Weil pairs or long exact sequence in such a category is assumed.

Step 4 applies `lem-a1-constructible-pullback-t-exact` to the geometric g, whose source and target are finite-type k-schemes. This node states t-exactness for every such morphism, so this step needs neither a new immersion-stability lemma nor a smoothness hypothesis on g. A t-exact pullback preserves the heart; placing that same heart object in degree zero is its canonical heart embedding, giving the displayed single-object comparison. The field-coefficient pullback comparison is Weil-equivariant by `fix-prop-coherence`. Substitution into the previously constructed arrow and the definition of R^r f! yields the sheaf claim, including its naturality and specified map.

For the edge cases, I checked the identity immersion (the comparison reduces to H^r of the identity-base-change exchange), the empty target immersion (both objects are zero by the same functorial construction), arbitrary negative r, zero K and shifts of a heart object. None of these is excluded by the proof; in particular r is never restricted to the natural numbers. Nonproper f is admitted by the compact-support clause throughout. The statement has no new hypothesis and no weakened clause. B1–B9 about newly introduced statements are vacuous because there are no new nodes; B10 was checked by the project-source searches above. C1–C4 are witnessed by the explicit statement quotes in citations.json; C5–C8 by the existing-node searches, dependency traversal, unchanged unit route and declared tool uses. D1–D5 are addressed by giving the cohomology composite in the item itself, without moving its content into new nodes. E1–E7 were checked against the exact coefficient domains, square corners and canonical maps described above. During this self-review I added the explicit `fix-lem-exchanges` citation so that naturality and the specified exchange are read directly from a statement, not inferred from a definition citation.

## Unfinished work

None for stage 1. New supporting theorem statements were unnecessary. The required server dry run and direct push follow this report.
