# Stage-1 delivery: lem-sfb-flat-graded-tail-proj

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-graded-tail-proj.json`: statement; split into eight steps, no full Mathlib match. Statement unchanged. The statement dependencies now also name finite presentation, finite locally free rank, projective space, module pullback, geometric fibres, quasi-coherence, graded algebras and Euler characteristic.
- No new nodes and no new Mathlib leaves.
- `citations.json`: one exact statement quotation for every citation of every proof step.
- `searches.jsonl`: actual msearch records for this attempt. The item's inherited searches are retained.

## Attachments

None. Searches for the exact blueprint tag and for flat graded tails and homogeneous localization colimits in `lean/WeilConjectures/` gave no declaration stating this item. The existing project declaration `AlgebraicGeometry.Scheme.Modules.finitePresentation_projective_sections` in `Modules/LocallyFreeAffine.lean` supplies only the already attached affine-sections tool, not the item. The HilbertPolynomial declarations concern coherent modules on proper schemes, not flatness from a graded tail.

## Literature and wanted sources

Read locally: Stacks `constructions.tex`, the standard charts preceding and in Tag 01M7 (`lemma-proj-sheaves`), Tag 01O3 (`lemma-relative-proj-base-change`), and Tag 07ZK (`lemma-surjective-generated-degree-1-map-relative-proj`); `algebra.tex`, Tag 05UT (`lemma-colimit-flat`); `morphisms.tex`, Tag 01U5 (`lemma-flat-characterize`), Tag 01TP (`definition-finite-presentation`), and Tag 01TX (`lemma-noetherian-finite-type-finite-presentation`); `coherent.tex`, Tag 0AG7 (`lemma-recover-tail-graded-module`); and `varieties.tex`, Tag 08AE (`lemma-hilbert-polynomial-H0`). Read the chapter and both the recorded unit and current main-20261015 unit. This is a subordinate Hilbert-construction prerequisite of the inherited alteration/direct-image branch, not a replacement of the unit's direct-image route.

WANTED: Grothendieck, Bourbaki Expose 221, printed p.262, proof of Lemma 3.3 (the item's inherited supplementary citation). That PDF is not present locally. The delivered proof does not depend on reading it: it is marked agent-written and uses the available Stacks text and existing DAG tools instead. No source was downloaded and no repository or launcher file was written.

## Findings and corrections

The original item had no proof. Its statement is correct as written, including the explicit permission for degree-zero equations. No STATEMENT-DISPUTED or statement correction is needed. All inherited source, ancestry and creation metadata are retained. `blueprint_refs.py ancestor` reports a null ancestor, matching the current node; I retained it and its detailed from.place/via rather than inventing an imported ancestor. Whole-blueprint searches for Hilbert polynomial, graded tail and homogeneous localization found no duplicate of the full item.

The potentially dangerous inference is cancellation by a coordinate. Step 4 instead uses the ordinary localization equality with an additional annihilating power; the transition maps need not be injective. Step 3 uses a separate finite locally free/projective argument in each degree, not a simultaneous trivialization of infinitely many graded components. Step 6 uses the image of the pulled-back ideal, not an asserted injection of its tensor pullback. Step 7 applies the Hilbert-function theorem to the polynomial ring and its cyclic quotient module, not to a quotient incorrectly assumed to have degree zero equal to the field in the unit-ideal case.

The initial self-review caught two implicit affine comparisons and made them explicit citations: the affine cokernel clause of `lem-weil-pbc-quasi-coherent-module-cokernel-image` in step 1, and `lem-weil-pbc-tilde-pullback-base-change` in step 6. I also made the relative-Proj/base-change model of projective space explicit in step 2 and corrected its source tag to 01WC/01TX.

## Not duplicates

No new nodes were created. In particular the needed unsaturated-coordinate-ring comparison already exists as `lem-sfb-projective-coordinate-ring-euler-polynomial`; I cite it rather than recreate Tag 0AG7 or the field clause of this item. Filtered-colimit flatness, arbitrary Proj base change, affine sections of finite locally free modules, and the eventual standard-graded Hilbert function likewise have existing nodes.

## Review by NO

I reviewed this split myself under the direct-delivery brief, with the source passages above and each cited node's statement open. This is the author's review; the maintainer's independent review remains the delivery review.

Step 1 takes exactly the surjective graded-map/closed-immersion clause from `prop-nagata-relative-proj-functoriality`, not its flat-base-change clause. `def-nagata-relative-projective-space` identifies polynomial relative Proj with projective space; `def-nagata-relative-proj` supplies its affine restrictions. `lem-weil-pbc-quasi-coherent-module-cokernel-image` explicitly says that a cokernel's sections on an affine are the quotient of sections, with the indicated kernel, so it supports the degreewise quotient algebra. `prop-nagata-proj-standard-open` gives the chart rings and covering, because degree-one coordinate images generate the irrelevant ideal even when the degree-zero unit map has a kernel. The source 01M7 describes exactly these homogeneous fractions; no assumption B_0=R is introduced.

Step 2 uses the equivalence of the projective-space models explicitly asserted in `def-nagata-projective-space-base-change`, and `def-kun-projective` is the finite-dimensional embedding convention required by `lem-kun-projective-implies-proper`. The latter states projective implies proper. `def-weil-proper-morphism` gives separatedness and finite type; `def-weil-finite-type-morphism` includes quasi-compactness. The base is locally Noetherian, precisely the hypothesis of `pqf-lem-lft-fp-locnoeth`, which therefore supplies local finite presentation. Applying `lem-weil-pbc-closed-immersion-proper` to the diagonal is legitimate since separatedness means this diagonal is a closed immersion. It is then quasi-compact by the same proper/finite-type definitions. `def-weil-quasi-separated-morphism` and `def-sbc-locally-finite-presentation` give quasi-separatedness and the three-part finite-presentation criterion. This argument requires no quasi-compactness or separatedness of the base itself.

Step 3 uses only the exact statements of `lem-pc-finite-flat-affine-sections-projective` and `lem-weil-pbc-projective-module-flat`: the first applies to a finite locally free module on an arbitrary scheme and any affine open, and the second to any projective module over a commutative ring. The given integer rank P(d) supplies finiteness independently in each degree. I read the attached project source declaration at LocallyFreeAffine.lean:71 as a cross-check of the first tool.

Step 4 is an elementary universal-property calculation from `def-nagata-homogeneous-localization-degree-zero` and `def-weil-ring-localization-away`. The former gives b/x_i^d with b of degree d, and the latter gives the annihilating-power equality test. Raising both representatives to one common degree proves independence without cancellation, then gives a unique linear map for any compatible cocone. This proves the colimit identification in the item rather than hiding it in a new lemma. The directed set is the small nonempty tail of the natural numbers; zero maps, zero rings and nilpotent coordinates cause no exception.

Step 5 takes flatness of this particular module colimit from `lem-weil-pbc-filtered-colimit-flat-modules`; its smallness, directedness and flatness hypotheses were all established. `lem-weil-pbc-flat-ring-map-iff-flat-affine` says exactly that flatness of each chart ring over R makes its Spec map flat. `def-weil-flat-morphism` is used only to identify flatness at each point with the same stalk map in the source and target open neighbourhoods, not as an unproved theorem about preservation of exactness by a nonflat tensor product.

Step 6 uses `lemma-nagata-relative-proj-base-change-arbitrary`, whose statement allows every base morphism, as the base-change theorem; the flat-only clause of the functoriality node is not substituted for it. `lem-weil-pbc-tilde-pullback-base-change` supplies the natural affine tensor model and its equation on m versus 1 tensor m. The ordinary quotient algebra formula is checked by its universal property on the variable images, without assuming flatness or injectivity of the tensor of J. `prop-nagata-relative-proj-functoriality` gives the quotient closed embedding after pullback. The homogeneous fraction definition makes the chart maps on b/x_i^d explicit, showing agreement as embedded closed subschemes of projective space. This also checks non-Noetherian T.

Step 7 uses `lem-trf-standard-graded-hilbert-function` exactly for the polynomial ring S and its finite graded module S/I, so its hypotheses S_0=k and finite generation hold even for I=(1). `lem-sfb-projective-coordinate-ring-euler-polynomial` explicitly permits unsaturated ideals and empty schemes, and explicitly gives the eventual equality of dim A_d with the Euler characteristic. Thus this is the existing comparison needed here, not just a definition of Hilbert polynomial or an assertion about saturated coordinate rings. I read its source 0AG7 and 08AE: the former gives eventual section comparison for a finite graded polynomial module, and the latter is the high-twist H0/Euler comparison. These statements explain why equality is eventual rather than a claim about every homogeneous degree.

Step 8 is elementary after steps 6 and 7. `def-weil-geometric-fibre` identifies the base change to an algebraic closure; `def-pc-module-pullback` and `def-amb-finite-locally-free-module` make the tensor of a local free frame an Omega-basis. Consequently each A_d has dimension P(d) for d>=m. The previously proved eventual polynomial equality and the finite-root property of nonzero rational polynomials give Q=P. No uniform frame in d is used.

For the B--E checklist: there are no new-node B1--B8 issues; all notions newly needed are existing definition dependencies. Every non-elementary input is a cited statement, and the quotation file contains its literal full statement. I checked every hypothesis used as described above, and the only elementary steps are the fraction universal property and the final rank/polynomial calculation. No step exceeds 2000 characters. Generic off-unit tools are declared in split_report.tool_uses; this does not replace a unit's prescribed route. No proof of a cited node is being mined for a stronger statement. No SGA source is used.

Edge cases checked directly: J=(1), irrelevant-primary ideals such as (x_0,...,x_n)^a, zero or nilpotent chart coordinates, P=0, m=0, n=0, the zero base ring and empty base, nonflat coefficient change R to R/a, and nonsaturated ideals with the same Proj but different low-degree pieces. In the n=0 case the sole chart is the same tail colimit; it may be empty, and there is no hidden positive-dimensional-fibre hypothesis. Degree-zero equations are never discarded.

## Unfinished work

None within this one-level split. All eight steps and all conclusion clauses are present; zero new unsplit obligations were introduced. Existing cited unsplit nodes remain their own items.

## Validation

The server-only `srvcheck.py ... review_split` passed the initial eight-step split with zero new nodes. Full deliver.py dry run and push follow after the strengthened affine citations and this report.
