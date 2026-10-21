## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-etale-immersion-shriek-normalization.json`: statement, split; seven proof steps; no Mathlib match for the whole item. The existing statement, source, provenance and blueprint ancestry were retained.
- `citations.json`: 18 step/node entries with verbatim portions of the cited statements.
- `searches.jsonl`: the search command's own five records; results read and added to the item's existing search history.

There are 0 new nodes and 0 new Mathlib leaves. `write_split.py` is a sandbox-only preparation script, not part of the delivered DAG.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and its extension-by-zero, compactification-comparison, closed-direct-image and normalization notions. I read the relevant `Derived/OpenImmersionLowerShriek.lean`, `UpperLowerStar/ClosedImmersion.lean`, `Derived/LowerShriek.lean`, `Derived/LowerShriekTransport.lean`, `Derived/LowerShriekIndependence.lean` and identity-comparison interfaces. These provide parts of the formalism, but I found no project declaration or collection of declarations stating every clause of this item, including its specified trivial-compactification normalization and change-of-choice equation. Thus I make no ATTACH claim.

## WANTED

None. The sources needed here are in `literature/stacks-project/`.

## What was wrong or missing

The item had a correct statement and no proof. Its source's closed-immersion stalk lemma is not by itself a module exactness theorem. I instead reuse the existing finite abelian direct-image exactness statement and explicitly transfer exactness through the faithful exact module-forgetful functor. This avoids introducing a second closed-stalk or closed-exactness node. The existing `lem-sc-closed-immersion-pushforward-exact` and `lem-weil-pbc-closed-pushforward-stalks` concern topological/Zariski sheaves and do not give the ordinary etale result used here.

No statement was changed, no source error was found, and no unit or chapter route was changed. The item remains a normalization tool for the opening/final chart-adjunction argument of `sk-prop-sf-rf-shriek-preservation`. Its blueprint `from.place` already specifies this place. Whole-blueprint searches for `03S5`, `0F7I`, `normalization of ordinary`, `exact functor` and `closed immersion`, together with whole-DAG source/title searches, supplied no blueprint node duplicating the whole item.

## What could not be finished

Nothing in the mathematical split remains open beyond the existing cited DAG nodes. This is stage 1: no Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. Existing nodes were reused for finite direct-image exactness, module forgetful exactness, exact open extension, exact derived factorization, the cohomology/bound comparison, properness, and compactification comparisons. In particular no new node restates either normalization clause of the item.

## Mathlib searches

The five fresh searches are exactly those logged by `msearch.py`: two LeanFinder phrasings, one Loogle pattern, one Mathlib/AlgebraicGeometry grep and one LeanSearch query. All services answered. The first phrasing returned Zariski scheme-module restrictions and unrelated topological algebra; those are not the small etale constant-coefficient categories. The second returned `Functor.mapDerivedCategoryFactors` and related exact-functor interfaces. I read `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`, including the termwise factorization, and reused the existing exact-functor DAG nodes instead of making new leaves. The finite-morphism characterization returned by LeanSearch is already represented by `lem-weil-pbc-closed-immersion-finite`; I checked `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, including its closed-immersion-to-finite instance. None of the hits gives the compactification normalization or its compatibility equation. The original item's search history was preserved.

## Review by N6

I read both occurrences of delivery-errors B through E, the three blueprint levels in SETUP, the chapter and unit records, and the current blueprint unit proof. For the item I read Stacks `more-etale.tex`, construction and proof at Tag 0F7I (`lemma-shriek-well-defined`), including the composition/coherence paragraph; the sanity check Tag 0F51 (`lemma-proper-f-shriek`); `etale-cohomology.tex` Tag 04FX (`lemma-stalk-pushforward-closed-immersion`), Tag 03S5 (`proposition-describe-jshriek`), and Tag 03QP (`proposition-finite-higher-direct-image-zero`); `derived.tex` Tag 015F (`lemma-right-derived-exact-functor`); `sites-modules.tex` Tags 03DA/03DB (`lemma-abelian`, `lemma-limits-colimits`); and the closed-immersion-finite lemma in `morphisms.tex`. I also read the old blueprint finite-direct-image-exact node, whose statement matches the Stacks finite-direct-image computation. There are no new nodes requiring separate source review.

Step 1 uses precisely four statements. `lem-weil-pbc-closed-immersion-finite` makes the given closed immersion finite. `lemma-weil-pbc-finite-direct-image-exact` states exactness on **abelian etale sheaves**, not modules, so I use only that clause. `lem-weil-pbc-module-direct-image-left-exact` explicitly says module direct image is additive and its underlying abelian functor is the ordinary abelian direct image. `lem-weil-pbc-module-sheaves-colimits-forgetful` says the forgetful functor is faithful and preserves kernels and cokernels. The proof writes out why this reflects zero objects and exactness. Thus a short exact module sequence can be tested after forgetting. Neither Noetherian nor finite coefficients are needed for this particular step; the hypotheses in the item suffice.

Step 2 uses `lem-weil-pbc-extension-by-zero-exact`, whose statement already covers arbitrary constant commutative coefficient rings, not just abelian sheaves, and `lem-weil-pbc-exact-functor-derived-factorization`, which gives descent of an exact functor on the **unbounded** derived categories, together with its termwise factorization. Step 1 supplies its exactness hypothesis for the closed case; the open exactness node supplies the other. The ambient abelian categories are those of ordinary constant-A module sheaves throughout.

Step 3 uses the statement of `lem-weil-pbc-exact-functor-bounded-below`, which explicitly gives the natural cohomology isomorphism and preservation of each standard lower bound. I checked that it does not merely assert preservation of some unspecified bound. The argument then notes that the same m works because additive functors preserve zero. This applies to unbounded inputs as well as bounded-below ones, exactly as the item requires.

Step 4 uses the sectionwise direct-image definition, the extension-presheaf definition, and the universal property of sheafification; I do not take an unmentioned plus construction from a definition node. For the identity open immersion every object factors uniquely, and for the identity direct image the fibre-product projection is an isomorphism. The inverse of the sheafification map of an existing sheaf follows by the two uniqueness equations. `lem-weil-pbc-localization-universal-property` explicitly includes descent and uniqueness of natural transformations and isomorphisms; it therefore supplies the derived identity normalization. `lem-weil-pbc-exact-functor-derived-functor` states that the canonical right-derived comparison is invertible for every complex, supplying R(id)_* = id with the chosen comparison, not just an abstract existence of an isomorphism.

Step 5 checks the two actual compactifications: (j,id_T) has proper identity second factor, and (id_Z,c) has proper closed second factor by `lem-weil-pbc-closed-immersion-proper` clause (a). The candidate formula in `def-amb-etale-compact-support` is Rr_* composed with Dj_!, and that definition expressly uses the unbounded K-injective total derived functor. The exact-functor comparison cited here is also unbounded; its inverse has direction Rc_* to Dc_* as required. The definitions yield the two e_a maps. The proof does not replace an arbitrary chosen compactification by a trivial one without a comparison.

Step 6 uses the full statement of `lem-amb-etale-compact-comparisons`: it gives natural coherent isomorphisms on bounded-below finite-module inputs, through common refinements and independently of the common refinement. The schemes here are Noetherian; all morphisms in question are separated finite type and compactifiable by hypothesis. Step 3 supplies the bounds needed in evaluating the trivial candidates. I define n_a explicitly as e_a composed with rho_(d,b_a). The candidate definition puts all components in the ambient unbounded category. No comparison theorem is applied to an unbounded input.

Step 7 is the elementary composition of the naturality squares already obtained and the cocycle equation explicitly stated by the compact-comparisons node. I wrote the equation n_a^(d') rho_(d,d') = n_a^d, with the order of composition matching the displayed source and target. This checks the content hidden by a bare word such as 'compatible'. It also proves compatibility for identity changes and proper refinements. Every step is under 1000 characters; there is no long step concealing a lemma.

For small cases I checked the zero coefficient ring and zero complexes (all functors and comparisons are on zero objects), identity open and closed immersions (both trivial candidates reduce to the identity), the empty open and empty closed source (zero source category and zero functor), and an arbitrary lower bound m with H^q = 0 for q < m. The closed argument does not assume a nonempty geometric fibre or incorrectly factor a general scheme through a closed subscheme from a point-set containment. There is no invertibility-of-ell assumption, torsion-free coefficient substitution, pro-etale comparison, or SGA route.

I compared every proof citation with its **statement**, not its proof. `citations.json` includes one verbatim entry per step/node citation. A read-only dependency traversal found no path from any used statement back to this item. Definitions and existing Mathlib leaves are used directly; all seven non-Mathlib off-unit statements have explicit generic-tool reasons in `split_report.tool_uses`. These support the unit's normalization step and do not replace its route. The review leaves the statement untouched and all imported/provenance fields intact. The mathematical work is ready for the independent maintainer reading after the required server checks.

## Validation

The first dry run stopped because the direct-image citation excerpt was below the audit tool's 40-character minimum. I expanded that excerpt to include the complete sectionwise direct-image definition and restriction maps; the proof did not change.
