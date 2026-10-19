# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-algebra-etale-near-field-or-dvr.json`: statement, split; no exact Mathlib match. The statement, statement dependencies, provenance, created record and other inherited metadata are unchanged.
- `citations.json`: sixteen quotations, one for each step/node citation, copied verbatim from the current DAG statements.
- `report.md`: this report. `searches.jsonl` is the required search command's log.

New nodes: 0. New Mathlib leaves: 0. All supporting facts already have DAG nodes.

## Attachments

None for this item. Searches for its blueprint tag and for its finite-algebra/DVR/torsion-free concepts in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration with its entire conclusion. Upstream master is reference material only. The existing closed declaration `AlgebraicGeometry.etale_SpecMap_algebraMap_tfae` (GroupScheme/Defs.lean:154) belongs to the already attached `lem-sc-finite-etale-algebra-criterion`; I read its signature and proof and reused its node, without making another attachment or another node.

## WANTED

None. The proof uses the local Stacks source already available.

## Problems found and corrections

The item was unsplit, not mathematically disputed. The statement needs no correction. The fact that the neighbourhood must be in the BASE is substantive: Mathlib's `Algebra.exists_etale_of_isEtaleAt` yields an element of the SOURCE algebra and cannot supply the requested conclusion directly. The proof now explicitly removes the closed image of the complement of fibrewise etale source neighbourhoods. It first spreads a free basis in order to apply the existing flat-family fibre criterion with genuinely global flatness on the smaller base.

Two existing source locators are imprecise but their statements give exactly what is used. `lem-sc-noetherian-finite-module-finite-presentation` cites a section tag 0517; the exact statement read in algebra.tex is 00FP(1), `lemma-Noetherian-finite-type-is-finite-presentation`. `lem-sbc-flat-fibre-etale-neighbourhoods` names 02GM (the all-fibres statement); the precise pointwise theorem read in morphisms.tex is 02GU(1) iff (2), `lemma-etale-at-point`. The steps cite these exact source places, and neither dependency node was edited.

The blueprint ancestry is retained: this is the finite algebra input to the Cohen–Gabber presentation, serving the local-duality part of Step 1 of `lem-per-artin-gabber-affine-curve`. I read the chapter and `sk-p-dl-a1-perverse` unit, the current ancestor proof and the parent Cohen–Gabber split. This algebra lemma does not change their route or the unit realization. Whole-blueprint searches for the title, “finite algebra etale” and field/DVR wording gave no duplicate blueprint statement. DAG searches also found the existing DVR freeness, free-at-prime spreading, finite field algebra criterion and closed finite image lemmas; these are reused. There are no new nodes to compare by tag.

## Unfinished work

None for this one-level stage-1 split. The existing supporting nodes retain their own proof status. No Lean was written or compiled; no compiler or Lake command was run; all authored files are inside this sandbox.

## Review by Q69

I read the item against Stacks morphisms.tex 02GU, `lemma-etale-at-point`, specifically conditions (1), (2), (4), (5), and algebra.tex 00U3, `lemma-etale-over-field`; I also read more-algebra.tex 0AUW(3), `lemma-dedekind-torsion-free-flat`, algebra.tex 0GWM, `lemma-finitely-presented-localization-free`, 00FP(1),(3), and morphisms.tex 01WN, `lemma-finite-proper`. The field-or-DVR hypothesis is only used for freeness at the marked prime. No excellence, normality, henselianity, perfect residue field, nonzero algebra or global flatness is silently assumed.

For Step 1 I opened `def-weil-pbc-module-localization` and `lem-sc-dvr-fg-torsionfree-free`. The former states the exact fraction zero criterion used to prove torsion-freeness after localizing; the latter states finite torsion-free over a DVR implies finite free. The nonzero numerator and denominator in the torsion argument are nonzero in the domain R. Finite module generators persist by their explicit fraction expressions. The field case is finite-dimensional basis selection, and the zero module has an empty basis.

For Step 2 I opened `lem-sc-noetherian-finite-module-finite-presentation` and `lem-weil-pbc-finitely-presented-free-at-prime-spreads`. The first really asserts module finite presentation over a Noetherian ring, and the second really assumes freeness at ONE prime and supplies an element outside that prime. I did not use `lem-sc-coherent-free-stalks-locally-free`, whose statement assumes freeness at every stalk. No step or part of the present lemma is hidden in a new node.

For Step 3 I opened all seven cited statements. `lem-weil-pbc-localization-noetherian` gives Noetherianity of R_g. `lem-weil-pbc-finite-type-noetherian-finite-presentation` gives algebra finite presentation, which is a different assertion from the module finite presentation in Step 2. Module generators are algebra generators by writing each element as their linear combination. `def-sbc-locally-finite-presentation` translates this on the displayed affine chart. `lem-sc-affine-standard-cover-finite-free-local-fp-flat` gives module flatness, and `lem-pc-affine-flat-module-local-criterion` says precisely that a module flat over R has the required localized flatness over every R_p; with M=B_g its localization is the source stalk. `def-weil-flat-morphism` therefore applies. `def-weil-finite-integral-morphism` gives the finite affine-algebra criterion. The proof does not infer flatness merely from the definition. The two non-closed generic off-unit tools (this flatness localization and the fibre criterion in Step 5) are declared in split_report.tool_uses; neither is a substitute route for the perverse unit.

For Step 4 I opened `lem-weil-pbc-fibre-product-affine-spectra` and the full statement of `lem-sc-finite-etale-algebra-criterion`. The former gives the SCHEME-THEORETIC fibre, whose ring is a tensor product, not B/pB. The latter explicitly contains both the zero-differential condition and the finite separable-product condition, with no group-scheme hypothesis on these first clauses. Finiteness of F follows by the displayed generating set. The fraction and tensor formulas explicitly check that shrinking at g preserves this same fibre and residue field. I also read the existing project's TFAE signature to confirm that the empty finite product is allowed.

For Step 5 I read `lem-sbc-flat-fibre-etale-neighbourhoods` and used its statement, not its proof: its hypotheses are exactly flat plus locally finitely presented, and it produces an etale SOURCE open at every point over the chosen base point. Those hypotheses were established in Step 3. Its source is made precise by 02GU(1) iff (2). Taking their union is elementary and also works for the empty fibre; I do not assert at this stage that the neighbourhoods are base opens.

For Step 6 I read `lem-weil-pbc-finite-closed-map-finite-fibres`, whose first clause explicitly says the image of EVERY closed subset is closed. It applies to Z, which is the complement of the union just constructed. The resulting closed image misses the marked base point, so the written ideal argument chooses an actual f in R outside p; it does not stop with an element of R_g or B. Restricting etale local presentations to opens and assembling them uses the local definition in `def-weil-etale-morphism`. The final paragraph checks why inverting f already inverts g, and hence why the resulting map is R_f to B_f. This is exactly the conclusion, without a finite-field or characteristic restriction.

I tested the statement on B=0 (empty product and empty fibre; every step still applies), B=R and B=R^n (finite free with separable fibres), the generic prime of a domain (the local base is a field), and a DVR at its closed point. A ramified quadratic DVR algebra has a nonreduced special fibre and fails the differential/separability assumption, as it should. R/(t) over a DVR is excluded by torsion-freeness; thus the freeness argument never applies to a vertical torsion component. Characteristic p purely inseparable finite field extensions fail both fibre conditions. The proof has six steps, all below 2,000 characters, and no inline comparison has been deferred by a word such as “standard” or “transport”.

Mathlib searches are the actual msearch commands in searches.jsonl: LeanFinder under two phrasings, Loogle, grep, and LeanSearch. I read every returned list and the Etale/Locus.lean source for the closest candidate. It supplies etale source principal opens from an already etale stalk; it does not combine the hypotheses or push a source open to a base open. The old item's search records are preserved, and the new log entries are recorded with the exact query texts and results. No unavailable search was represented as a negative result.

I checked delivery-errors B–E against the written files: there are no new statement-only nodes, no duplicate/restatement nodes, no changed target or item statement, and every non-elementary step names the facts it uses. Each of the sixteen citations has the verbatim statement in citations.json. Dependencies are exactly the union of step uses; statement dependencies are retained because the statement is unchanged. The dry run and push outcomes are recorded below when they finish.
