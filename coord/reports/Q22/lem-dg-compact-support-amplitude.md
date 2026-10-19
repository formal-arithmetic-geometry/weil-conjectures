## Files written

- `dag/nodes/sec-smooth-purity/lem-dg-compact-support-amplitude.json`: the imported item, now split with nine proof steps; no new nodes.
- `citations.json`: 39 verbatim statement quotations for the item's proof steps.
- `report.md`: this report.

No Mathlib leaves or new unsplit nodes were created. The four required Mathlib searches were run for the item itself: LeanFinder returned only unrelated derived-category support lemmas, Loogle and Mathlib grep returned no relevant declaration, and LeanSearch was unavailable; these are recorded in the item's `mathlib_searches` exactly as run.

## Attachments

None. A grep of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: lem-dg-compact-support-amplitude)` and no declaration stating this compact-support amplitude result.

## WANTED

- `literature/stacks-project/varieties.tex`, Stacks Tag 0A21 (Lemma 33.20.3, part (3)), for the dimension equality for a nonempty open in an integral finite-type scheme over a field. The existing DAG node `lem-sc-integral-locally-algebraic-opens-dimension` records this source and was cited directly.
- `literature/stacks-project/etale-cohomology.tex`, Stacks Tags 04CA, 03S5 and 035C/0A5D, for closed-immersion pushforward, extension-by-zero stalks, finite pushforward cohomology, and their étale-site formulations. Existing DAG nodes record these sources and were cited directly.

## What I checked and corrected

The imported two-paragraph sketch did not specify the coefficient-forgetting comparison, the general derived proper-base-change clause, the finite-type/Noetherian hypotheses needed for the compactification, the empty-fibre case, or why the reduced closure has dimension bounded by the original fibre. I made these explicit in the item proof. I retained the original fibre `U=X_{\bar y}` throughout; the compactified fibre `T=\overline X_{\bar y}` is used only as an ambient proper scheme, and the closed support `C` is the reduced closure of `U`.

The proof now uses the existing nodes for Nagata compactification, compact-support construction and comparison, geometric-fibre base change, extension-by-zero base change and stalks, exact inverse image, module/abelian cohomology comparison, reduced induced closed subschemes, finite closed pushforward, the integral-open dimension theorem, torsion cohomological dimension over separably closed fields, and conservative geometric stalks. I read each cited node's statement before quoting it; `citations.json` contains the full verbatim statement for every citation, so each step is checked against what that node actually says.

I checked the hypotheses at the relevant steps: finite type over a field implies Noetherian; proper base change preserves properness; the reduced closure has finitely many irreducible components; each component meets the dense original fibre; each such component is integral finite type over the algebraically closed residue field; the coefficient exponent makes the supported sheaf torsion; and the geometric-fibre dimension hypothesis applies to `U`, not to `T`. I separately handled `U=\varnothing`, where extension by zero is zero. The Stacks 0A21 argument was tested on the edge cases of an integral point (dimension zero), an affine line with a punctured open, and the empty fibre (handled separately because the theorem requires a nonempty open).

The final step applies stalk conservativity to the underlying abelian sheaf and then observes that a module sheaf with zero underlying abelian sheaf is zero. This preserves the statement's original ordinary-derived-category interpretation and does not introduce a bound on the compactification.

## Review by Q22

I read the item node, its unit and chapter records, the imported blueprint proof, and the relevant source declarations in `/home/ubuntu/weil-src-slopmaster2`. The source search found no finished declaration for this item. I read all statements of the 39 nodes cited by the nine steps and copied them verbatim into `citations.json`; in particular I checked that the proper-base-change node is used for the derived stalk formula, that the finite-pushforward node actually gives cohomology invariance (rather than only exactness), and that the extension-by-zero node gives the support stalk calculation.

Step 1 checks Noetherianity and compactification before invoking the compact-support definition and the bounded-below/unbounded resolution agreement. Step 2 checks base change of the open immersion, the derived proper-fibre stalk calculation, exact inverse image, and module-to-abelian cohomology. Steps 3–5 construct the reduced closure, bound each component by the original fibre via the integral-open dimension theorem, and pass to the whole closed support including the empty case. Steps 6–7 identify the supported sheaf as a finite closed pushforward and transfer cohomology to the support. Step 8 applies the torsion cohomological-dimension theorem over the algebraically/separably closed residue field. Step 9 uses geometric-stalk conservativity to conclude the sheaf vanishes.

I checked each hypothesis where it is used and corrected the imported proof's implicit assumptions. No new node was needed: every non-elementary fact was already stated by an existing DAG node, and the one-line dimension and empty-support observations are marked elementary only where they follow directly from cited statements and definitions. The item remains on the blueprint route and its statement is unchanged.

## Dry run

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q22 lem-dg-compact-support-amplitude --no-push` completed successfully after the repository preflight queue cleared: `OK (not pushed) deliver/Q22/lem-dg-compact-support-amplitude at bd4e0fc77f: preflight passed`. An earlier concurrent preflight reported an inherited route finding on `prop-cohomological-finiteness`; a refreshed run passed with no finding on this item.

## Second reading by Q22

- Step 1: checked the compactification and ordinary-derived-category hypotheses against the item statement and the cited Nagata, compact-support, and injective-resolution nodes; verdict: valid.
- Step 2: checked the geometric-fibre base-change clause, open-immersion base change, exact inverse image, stalk calculation, and module-to-abelian comparison against all seven cited statements; verdict: valid for the stated bounded-below input.
- Step 3: checked properness, finite type, reduced induced support, finite irreducible components, and integral component structures against the seven cited statements; verdict: valid after tightening the component-intersection argument.
- Step 4: checked the nonempty-open dimension equality and the Krull-dimension comparison against the cited dimension statements and the source's Tag 0A21 clause; verdict: valid, with the original fibre dimension bound used only for the closed open pieces.
- Step 5: checked the component-to-support dimension passage and the empty-support case against the cited Krull-dimension, extension-by-zero stalk, conservative-stalk, and zero-cohomology statements; verdict: valid.
- Step 6: checked support detection by geometric stalks, closed-immersion pushforward, and torsion transfer through inverse image against the cited statements; verdict: valid.
- Step 7: checked finiteness of the closed immersion and the finite-pushforward cohomology isomorphism against the two cited statements; verdict: valid.
- Step 8: checked separable closedness of the algebraic closure, the torsion cohomological-dimension convention, and the finite-type bound against the three cited statements; verdict: valid for the globally exponent-killed sheaf constructed in step 6.
- Step 9: checked independence and conservativity of geometric stalks against the two cited statements; verdict: valid, and the final zero-underlying-sheaf observation is elementary.
- New nodes: none; every dependency is an existing DAG node, so B1–B7 and duplicate-node checks are vacuous.

Changes made: repaired step 3's assertion that a component-minus-the-other-components is open in the whole support. The revised argument uses that, if a component missed the original fibre, the fibre would lie in the finite union of the other closed components, forcing its closure to do so and contradicting maximality. No statement, hypothesis, source citation, or citation quotation changed.
