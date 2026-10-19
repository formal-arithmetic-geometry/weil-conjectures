# Q85 stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-etale-local-compact-support-extension.json`: existing ten-step statement split retained from the shared DAG; status corrected from `unsplit` to `split`.
- No new node files were created. The proof cites existing DAG nodes, including the previously split `lem-cbc-zariski-enhanced-derived-descent` and the existing unsplit generic coherence nodes.
- `citations.json`: 51 step/node entries with verbatim statement quotes.

## Attachments

None. The item's Lean audit is `none` for the master and slopmaster2 source, and no sorry-free project declaration was found that states this item.

## WANTED

None.

## What was wrong or incomplete

The shared item already contained the complete affine-local construction, proof steps, provenance, blueprint reference, tool-use declarations, and Mathlib search history, but its status remained `unsplit`. I retained that proof and changed only the status to `split`; no statement or hypothesis was changed. I also supplied the required citation map and this independent review. The long refinement calculation in step 9 was checked as one typed mate-pasting argument: it uses the existing proper/open coherence and mate-pasting statements rather than hiding an uncited lemma.

## Review by Q85

I read the item node, its chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`, the ancestor blueprint proof for `thm-cbc-finite-level-proetale`, and the Stacks source `literature/stacks-project/more-etale.tex` at Tags 0F7I, 0F7L and 0F7H. The statement agrees with the stated construction: finite commutative coefficients, bounded-below etale derived categories, separated finite-type maps over arbitrary schemes, affine-local compactifications, restriction and refinement comparisons, and the exchange transformation with its restriction and compactification formula. I checked that no global compactification, quasi-compact base, or quasi-separated base is assumed.

For step 1 I opened the cited affine-basis, separated finite-type base-change, finite-type convention, separated-to-quasi-separated, qcqs-over-affine, Nagata compactification-category, and universe-size statements. They provide exactly the basis, morphism hypotheses, qcqs hypotheses, nonempty cofiltered compactification category, refinement/base-change closure, and small-skeleton choice used there. The empty-base clause is the zero-category case.

For step 2 I read the inverse-image exactness, semilinear enhanced-section, DG localization, proper-support sheaf-composition, and proper/open coherence statements. They provide the constant coefficient identification, enhanced operations and mates, strict coherence preservation, the actual support-subsheaf comparison, and the required vertical, horizontal, and base-change diagrams. The displayed injective-resolution arrow is the normalization specified by the coherence node.

For step 3 I checked the proper/open normalization, proper-open comparison, cofiltered coherent-equivalence, and Nagata statements. They say that the refinement arrows are the prescribed `Rp_* alpha` maps, are equivalences with identity and composition coherence, and admit the required homotopy-colimit cone; the opposite filtered indexing is the correct variance.

For step 4 I checked the Nagata base-change, derived-open-restriction, extension-zero base-change, proper/open coherence, semilinear mate, coherent-equivalence, and affine-basis statements. Their hypotheses match affine inclusions and pulled-back compactifications. They supply compatibility with refinements, iterated restrictions, and affine overlaps; no intersection of arbitrary affine opens is assumed affine.

For step 5 I checked extension-by-zero exactness, bounded-below injective representatives, enough injectives, the direct-image definition, and inverse-image exactness. These statements justify preservation of the same lower bound by each local compactification functor and its uniformity over an infinite affine basis.

For step 6 I checked the enhanced Zariski descent statement and size convention. Its functor-category equivalence is exactly the stated tool for gluing the coherent affine-basis system, preserving the lower-bound subcategories, and producing the restriction comparisons and their identity/iteration equations before passing to ordinary derived categories.

For step 7 I read proper base-change, open-immersion base-change, qcqs-morphism permanence, derived-open-restriction, extension-zero base-change, and enhanced descent. Properness, openness, and quasi-compactness survive restriction with the cited hypotheses, and the cone equations descend simultaneously for all global compactifications and refinements. No faithfulness of ordinary restriction is used.

For step 8 I checked the affine-basis, Nagata, separated finite-type base-change, exchange-map, semilinear mate, and inverse-image exactness statements. Affine subopens of inverse images cover the arbitrary base, and the displayed exchange composite has the prescribed direction and remains bounded below; no qcqs assumption on the inverse image is introduced.

For step 9 I read the proper/open coherence and mate-pasting statements in full. The definitions of `delta_w`, `beta_i`, and `E_i` make every source and target explicit. The two displayed equations are the exact refinement and composition-adjunction identities supplied by those nodes; substitution gives the claimed equation in the prescribed direction. The final affine-overlap argument is the basis-descent compatibility, with higher overlaps inherited from the retained coherent diagrams.

For step 10 I checked the enhanced descent statement and the exchange-map definition. It identifies the descended source and target systems, gives naturality and restriction compatibility, and specializes on a compactified open to the proper-exchange followed by extension-by-zero formula. The item’s Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) were read and rerun for this delivery; they found only unrelated ordinary scheme/derived-category APIs, so no Mathlib leaf applies.

I tested edge cases in the proof text: the empty base is explicitly handled, an infinite affine basis is allowed because the lower bound is uniform, and affine opens of a non-qc inverse image are used rather than assuming the inverse image itself affine or qcqs. All 51 citation quotes are verbatim substrings of their cited node statements.
