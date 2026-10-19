## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-connected-fibre-open-spreading.json`: item split into nine steps following Stacks 055W; statement unchanged, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-lfp-cm-locus-fibre-dense.json`: statement-only supporting lemma, Stacks 045U(1),(3); not in Mathlib after two semantic phrasings, Loogle, LeanSearch and source grep.
- `dag/nodes/sec-trace-formula/lem-trf-cm-closed-point-flat-quasifinite-slice.json`: statement-only supporting lemma, the globally flat specialization of Stacks 0570 with the regular-immersion conclusion forgotten; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-locally-free-multisection-connected-open.json`: statement-only supporting lemma, Stacks 057I; no Mathlib match.
- `citations.json`: one entry for every cited node in every item proof step, quoting its actual statement verbatim.
- `searches.jsonl`: actual search-command results, retained with their tool/query/digest; earlier searches in the item's record have also been retained.

## Attachments

None. Searched WeilConjectures in the slopmaster2 and upstream master source checkouts by the item tag and geometric-connectedness/open-spreading terms. Also read the related slopmaster2 `AlgebraicGeometry/Morphisms/SlicingFlat.lean` and searched `Slicing.lean`. Its slicing theorem gives an etale cover with connected-factorization charts, not an elementary base neighbourhood recovering an entire prescribed fibre open. It does not attach to this item or supply the finite-locally-free multisection descent assertion. No Lean was written and no compiler was run.

## WANTED

None. All primary mathematical inputs are present in the local Stacks source.

## Faults and corrections

The item's statement agrees with 055W: finite presentation includes quasi-separatedness; connected means nonempty; the base neighbourhood is affine and elementary (residue field isomorphic); and the designated open is recovered in its entirety. No statement dispute or correction was required. The original item had no proof.

The terse source proof suppresses two arguments that are now explicit. The fibre open is quasi-compact because the finite-type fibre has a finite cover by Noetherian affine spaces; its lift is then a finite union of affine opens in an ambient open. The last affine base restriction preserves quasi-compactness because its map from the already quasi-compact open to the affine intermediate base is quasi-compact. I did not assume that the inverse image of an arbitrary open is quasi-compact.

The source's closed Cohen–Macaulay point choice requires density as well as openness. Existing `lem-sbc-fibre-cohen-macaulay-locus-open` supplies only openness. I added only the missing density assertion and used the existing Jacobson-space leaf to obtain a closed point. The slice's residue extension need not be separable. The geometric-reducedness hypothesis alone is not used to assert that every point is smooth or Cohen–Macaulay.

## Unfinished work

None in this one-level split. The three new lemmas intentionally have no proofs and remain `unsplit` for later workers. There are zero new Mathlib leaves.

## Not duplicates

lem-trf-flat-lfp-cm-locus-fibre-dense vs lem-sbc-fibre-cohen-macaulay-locus-open: the existing statement asserts openness of the fibrewise depth-equals-dimension locus, with no fibrewise density conclusion; the new statement asserts density in every fibre, with no openness assertion.

lem-trf-flat-lfp-cm-locus-fibre-dense vs lem-sbc-restricted-fibre-cohen-macaulay-locus-open: the existing statement is openness after restricting to an open in the base, not density in each fibre.

lem-trf-flat-lfp-cm-locus-fibre-dense vs lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk: the existing statement produces a neighbourhood of constant local topological fibre dimension around a point with zero-dimensional fibre local ring; it does not assert density of Cohen–Macaulay points.

lem-trf-flat-lfp-cm-locus-fibre-dense vs lem-sbc-flat-fibre-dimension-strata-core: the existing dense family of opens controls local topological fibre dimension, and its statement contains no Cohen–Macaulay conclusion. Its proof cannot be used as a stronger statement.

The CM slice has no existing node with source Tag 0570; the finite-locally-free descent lemma has no existing node with source Tag 057I. Whole-DAG searches included the exact labels, tags, and Cohen–Macaulay, slicing, finite locally free and connected-fibre terms. Whole-blueprint searches using `tools/blueprint_refs.py` for `045U`, `0570`, `057I`, `Cohen`, `descent-connected-fibres`, `flat.*slice`, and the geometric-connected-fibre statement found no duplicate assertion. `lem-sbc-flat-reduced-etale-connected-charts` gives covering charts, not a quasi-compact open preserving the entire designated fibre under an elementary base change. The already reviewed parent `lem-trf-geometrically-integral-fibre-neighbourhood` is a smooth/geometrically-irreducible specialization with geometrically integral conclusion, uses this item, and must not be cited backwards. The stronger conclusions in the slice's Stacks source were deliberately not packaged as extra unused nodes.

## Review by Q09

I read `more-morphisms.tex` at `lemma-fibre-geometrically-connected-reduced` (055W), `lemma-flat-finite-presentation-CM-open` (045U), `lemma-slice-CM` (0570), `lemma-etale-makes-quasi-finite-finite-at-point` (02LK), and the entire statement and proof of `lemma-descent-connected-fibres` (057I). The three new nodes respectively state 045U's density assertion, the exact portion of 0570 needed by 055W, and all of 057I's hypotheses and conclusions. In particular the last permits empty fibres away from the specified point. Their statements are self-contained and definition dependencies account for depth, dimension, Noetherian rings, closed points, fibres, flatness, finite presentation, quasi-finiteness and finite local freeness. They carry no proof, no proof dependency, no hidden proof sketch and no Mathlib match. Every recorded new-node search was actually run by msearch; all services returned results and none was silently treated as unavailable or absent. The grep found no Cohen–Macaulay formalism, and the semantic hits concerned flatness, going down, smooth charts, finite/discrete fibres, or generic descent properties, rather than the three asserted results.

For step 1 I opened the affine-open basis, flat base-change and qcqs-permanence statements: they supply precisely the affine base replacement and preservation of flat finite presentation. The base-change definition explicitly includes iterated pullbacks. Source and target open restrictions preserve the etale local charts, so the eventual neighbourhood still lies over the original base with the same residue map.

For step 2 I checked that the fibre definition actually asserts the homeomorphism onto the inverse-image subspace, not just the scheme fibre construction. The affine Noetherian leaf says that spectra of finite-type field algebras have stabilizing closed chains, which is exactly what the finite-subcover argument uses. The finite-presentation definition supplies finitely generated fibre algebras, the permanence node supplies quasi-compact base changes, and the affine qcqs leaf supplies quasi-compact affine charts. The affine-basis statement then gives an honest ambient open lift, and finitely many affine opens cover the whole specified T. This proves equality as open subschemes, not just containment or a nonempty subopen.

For step 3 I read both directions of the quasi-separated affine-cover criterion, the affine qcqs statement and the three clauses of qcqs permanence. Affine opens of the restricted W are affine opens of Y, so their intersections remain quasi-compact and the converse criterion makes W quasi-separated. I checked local ring maps are unchanged on opens, finite presentation is inherited on principal affine subcharts, and reducedness is a local-ring property even after arbitrary field extension. This justifies every hypothesis carried into the rest of the proof without assuming the family separated or Noetherian over the original base.

For step 4 I compared the actual openness statement with the new density-only statement, then used the Jacobson leaf with closed subset all of the finite-type fibre. Nonemptiness follows from the connectedness convention. Density plus openness gives a nonempty open of the fibre, and density of its closed points gives a point closed in the whole fibre. Neither smoothness nor a separable residue extension is claimed.

For step 5 the new slice is applied only after flatness, local finite presentation, closedness in the fibre, and the Cohen–Macaulay fibre local ring were established. Its singleton fibre supplies an isolated point. The existing 02LK node requires local finite type and an isolated fibre point, both now hold, and explicitly supplies the etale neighbourhood, residue isomorphism, finite open piece and unique point above the designated base point. I did not infer local finite type from an unrelated finiteness hypothesis.

For step 6 the persistence node explicitly permits further base maps preserving the designated residue field, so an affine open inclusion is allowed. Its finite and unique-point clauses justify the refinement. Flat base change and lfp base change apply to the slice, and their source-open restrictions use the same local calculations as step 3. I opened `def-pc-finite-locally-free`: it defines the notion as finite, flat and lfp, so no theorem about a finite locally free module or its rank is being smuggled into a definition citation.

For step 7 I checked the flat and finite-presentation base changes apply to the modified family and wrote the fibre after any extension L of kappa(t) as the original fibre extended to L. This checks geometric reducedness for arbitrary points of U. The designated fibre is the entire T extended to kappa(u), with connectedness surviving all further field extensions by the geometric-connectedness definition.

For step 8 I checked every hypothesis against the literal new 057I statement: the E-to-Y_U map is over U; E-to-U is finite locally free with nonempty fibre over u; Y_U-to-U is flat of finite presentation with geometrically reduced fibres; and its entire u-fibre is geometrically connected. The conclusion gives a quasi-compact open, exact equality of the designated fibre, and connectedness only for nonempty fibres. The argument that removes empty fibres remains in the item's proof rather than being moved into a restated clause node.

For step 9 the flat-lfp open-map leaf states openness for scheme morphisms and every base change, not merely ring spectra. Its application is to the open restriction of the modified family. An affine neighbourhood inside the image exists by the basis leaf. The qcqs-permanence statement gives quasi-compactness of V^0-to-U because U is affine/quasi-separated; the separate preimage-of-qc-open leaf gives quasi-compactness after the final affine restriction. Residue fields of open neighbourhoods do not change, so every fibre there is the same connected nonempty fibre, and iterated base change gives the exact requested open T. All source opens compose to an open in the original family.

I tested the new statements and the proof on a base field with a reducible connected nodal curve (connected must not be replaced by irreducible), relative dimension zero (the slice can be an open with singleton fibre), a purely inseparable finite residue extension (no separability hypothesis), and an affine line over a possibly non-Noetherian base (no Noetherian-base assumption). For the density node, empty fibres have vacuous density and non-Cohen–Macaulay fibres may have nonempty dense Cohen–Macaulay opens; it does not assert the whole fibre is Cohen–Macaulay. For the descent node, a finite locally free map may have rank zero on other base components, so nonemptiness is imposed only at the designated point and empty output fibres are allowed until the final base shrinking. An empty T is excluded by the item's explicit convention, as required to choose the point and keep the final base neighbourhood.

I checked B–E of delivery-errors with these files open: no relabelling of an item clause, no proof imported from another node's internals, no backward citation to the parent, and no source outside the permitted route. Every proof step is below 2000 characters. The geometric tools from other units are declared in split_report.tool_uses; the existing Mathlib leaves need no route exception. No chapter or unit record was changed. This is direct self-reviewed delivery as authorized by the brief; the independent maintainer review remains the next reading.
