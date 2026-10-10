1. Files written

- `dag/nodes/sec-curve-estimates/etale-proposition-etale-reduced.json`: new unsplit statement node; Mathlib no match.
- `dag/nodes/sec-curve-estimates/lem-sc-brauer-zero-all-curves.json`: repaired and marked `split`.

2. Attachments

- None for the item: `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup` still contains `sorry`.
- `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite` belongs to `lemma-weil-pbc-finite-direct-image-exact`.
- `AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite` belongs to `lem-weil-pbc-finite-pushforward-cohomology`.

3. WANTED:

- None. The imported proof cites Grothendieck and Milne for the classical smooth-curve input, but the existing DAG node `lem-sc-brauer-zero` supplies that route and no document download is needed for this split.

## Review by C1

I read the item source `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-brauer-zero-all-curves.md`, the chapter and unit records, and the Lean declaration in `WeilConjectures/AlgebraicGeometry/Curve/Brauer.lean` (lines 179–191). The Lean theorem has a `sorry`, and its statement is the cohomological Brauer vanishing claimed by the item, so it is not an attachment. For the new node I checked the Stacks tag index entry `025O, etale-proposition-etale-reduced`; its source is `literature/stacks-project/etale.tex`, Proposition 025O. I also searched slopmaster2 first (B10): no declaration states this scheme-level result without a sorry.

The opening step uses `lemma-weil-pbc-finite-direct-image-exact` and `lem-weil-pbc-finite-pushforward-cohomology`; I checked their statements and sorry-free declarations in `WeilConjectures/SixFunctors/Finite/Exact.lean` and `WeilConjectures/AlgebraicGeometry/Sites/CohomologyClopen.lean`, including their use for closed immersions and the finite normalization map. Step 1 follows the blueprint nilradical filtration: `def-sc-etale-qcoherent-module` supplies the etale sheaves, and `etale-proposition-etale-reduced` is cited for the etale pullback of the reduced subscheme. In the cohomology claim, `lem-sc-etale-affine-qcoherent` and `lem-sc-cech-spectral` give the etale Cech comparison, `pqf-lem-affine-vanishing` gives the Zariski affine-intersection vanishing, and `lem-sc-noetherian-cohomology-above-dimension` gives vanishing above dimension; I checked their statements and the hypotheses used here (`C` is Noetherian, separated, and has dimension at most one). Step 2 follows the normalization source: `def-sc-normalization`, `lem-sc-normalization-exists`, and `lem-sc-normalized-curve-smooth` provide the component normalizations and smoothness; `etale-proposition-etale-reduced` supplies reducedness of each etale `V` over reduced `C`; `lem-kun-03qu-sep-closed` gives vanishing for both the coefficient sheaf `(i_Z^*Q)_z` and the `G_m` factors on `Spec k`; and `lem-sc-brauer-zero` supplies the smooth connected curve case. I checked every cited node exists, is unmerged, and states the fact used at its step.

I corrected the returned proof by adding the missing reducedness node and citing it in both uses, replacing the two unsupported literature phrases in the claim with the existing affine and Noetherian vanishing nodes, and replacing the constant-sheaf point-cohomology citation with the all-coefficients separably closed point node. I updated `proof_deps` and `split_report.tool_uses` accordingly. I checked the edge cases: zero-dimensional normalization components are `Spec k`, disconnected and singular curves are handled componentwise, the nilradical filtration is trivial for a reduced curve, and empty point support makes the point product vacuous. The new node records LeanSearch, LeanFinder, and Mathlib-source grep searches, all with no match.

5. What could not be finished

- The theorem itself remains a `sorry` in slopmaster2; this stage only splits the natural-language DAG and does not write Lean proofs.
