# Stage-1 report: prop-pur-affine-line-orientation-base-change

## Files written

- `dag/nodes/sec-smooth-purity/prop-pur-affine-line-orientation-base-change.json`: restored as a split statement node with the unit's prescribed one-step proof route.
- `citations.json`: seven verbatim statement quotes for the seven nodes cited by step 1.
- `report.md`: this worker report.

No new nodes and no Mathlib leaves were created. The existing item search records were retained; no new search was needed for a newly created node.

## Attachments

None. I checked the declarations tagged `(blueprint: prop-pur-affine-line-orientation-base-change)` in the read-only source, especially `AlgebraicGeometry.Etale.supportedClassMap_restrictSupportedClass_affineLineOrientation` and `AlgebraicGeometry.Etale.restrictAffineLineZeroLocusHom_affineLineOrientation` in `WeilConjectures/EtaleCohomology/Purity/Smooth/Orientation.lean` (the docstrings and declarations around lines 212–283). They use the source library's abstract `HasKummerClass`/ordinary-etale presentation and its explicitly defined restriction morphism. The item here is the fixed purity-datum statement about `Lv^*` and the exceptional comparison in the pro-etale coefficient setting, so those declarations were used as source corroboration rather than attached as an exact finished declaration.

## WANTED

None. The blueprint proof and unit route were read from the imported blueprint records and checked against the corresponding source docstrings in `Orientation.lean` and `KummerBaseChange.lean`; no source was treated as unavailable.

## Problems corrected

The returned version had replaced the `sk-prop-a1` route with a longer supported-Chern-class and ambient-adjunction construction without establishing a mathematical error in the prescribed route. I removed that replacement and restored the route in the blueprint proof: identify the exceptional base-change source and target, check the pulled-back Kummer boundary on each geometric fibre, use the rank-one normalization, and invoke global uniqueness.

The returned version also put a cross-unit `tool_uses` list in worker metadata. That field is maintainer-owned, so it was removed from both the node and its `split_report`. The proof cites the seven route statements directly; it does not claim maintainer approval for any tool use.

The prior report incorrectly said that the blueprint sources were unavailable and listed them as `WANTED`. That claim and those entries were removed. The source route was checked against the blueprint-derived node records and the read-only Lean docstrings, including the explicit Kummer-boundary base-change theorem.

## What could not be finished

Nothing remains in the stage-1 split. No Lean was written, compiled, or built, and no live project or launcher file was modified.

## Review by NV

I reread the item statement, the `sk-prop-a1` unit record, the blueprint proof route, and the source docstrings in `Orientation.lean` and `KummerBaseChange.lean`. The item keeps the fixed hypotheses `\Lambda=A`, the separated finite-type `k`-scheme affine-line datum, and an arbitrary morphism `v:Y'\to Y`. The source's `restrictSupportedClass`/`restrictAffineLineZeroLocusHom` descriptions confirm that the comparison in the item is the exceptional base-change map for the Cartesian square of zero sections.

Step 1 cites `def-weil-exceptional-adjoint-admissibility` for the mate comparison convention of the exceptional inverse-image formalism; its statement supplies the coefficient-stage comparison maps as adjunction mates of compact-support comparisons. It cites `def-pur-affine-line-datum` for the two affine lines, their zero sections, coordinate, and Kummer class. It cites `lem-pur-gysin-structure` for the bounded, degree-zero support object and for the identification of the Kummer boundary with a morphism from the constant sheaf. It cites `lem-pur-kummer-coefficient-base-change` for compatibility of the Kummer boundary with pullback after coefficient extension; the fibre is a smooth separated affine line over an algebraically closed field, so that node's hypotheses hold. It cites `thm-pur-rank-one-local-calculation` for the residue of the coordinate being exactly the normalized class `1` on every geometric fibre. It cites `thm-pur-affine-line-orientation` for the global orientation and its normalized fibre restrictions, and `prop-pur-affine-line-orientation-uniqueness` for injectivity of restriction to geometric points and uniqueness of the normalized global morphism. The step is not elementary because it combines these seven statements; `elementary` is therefore `false`.

I opened each cited node and copied its complete statement into `citations.json`; each quote is verbatim and the proof dependency list is exactly the union of the step's uses. The geometric-fibre check preserves the arbitrary base morphism and does not assume that `Y` or `Y'` is reduced, smooth, connected, or flat. The coefficient hypothesis remains the one already imposed by the affine-line datum (including the finite-level twist condition). I checked identity base change, a field base, a disconnected finite-type base, and the nonreduced dual-number base; the coordinate fibre and its normalized Kummer residue behave as stated in each case.

This repair directly addresses every returned point: the prescribed route is restored, worker metadata contains no cross-unit `tool_uses`, and the blueprint/source availability claim is corrected.

## Second reading by NV

I read the actual master blueprint item and `sk-prop-a1/_section.md` over read-only SSH at `~/weil-newtargets/literature/blueprint/master/blueprint/sec-smooth-purity/`, as well as the source files for the supported-Hom lemma, support exactness, relative Kummer theorem, Gysin structure, global orientation and uniqueness. I compared them with the current shared DAG statements, including the repaired geometric-point clause of `prop-pur-gm-relative-kummer`. The item has no Stacks-tag source and this delivery creates no nodes requiring a tag/label audit. The ordinary-etale declarations in `Orientation.lean:212–283` and `KummerBaseChange.lean:230–275` corroborate the map and its direction; I did not treat them, their abstract Kummer hypotheses, or the upstream master sorry declarations as a finished pro-etale proof.

- Item statement: checked against the actual blueprint statement, `def-pur-conventions`, `def-pur-affine-line-datum`, and `Orientation.lean:212–283`; unchanged, including the fixed finite coefficient category and arbitrary morphism within the separated finite-type base setting.
- Step 1: checked against the affine-line datum's affine charts; the tensor quotient calculation proves the Cartesian square and coordinate pullback over arbitrary rings. Elementary, including zero rings and nonreduced bases.
- Step 2: checked closed-immersion properness, identity-open compactification, the constructible exceptional inverse-image definition and `thm-sf-ambient-adjoint-class` clause (2); the Gysin lisse degree-zero object and `lem-sf-proetale-constructible-origin` supply the actual bounded etale-origin witnesses required by `thm-cbc-finite-level-proetale`. The mate is the transpose in `def-weil-pbc-adjunction-mate`, in the direction `Lv^*Rs^! -> Rs'^!Lg^*`; verdict repaired, with no assumption that an arbitrary exceptional comparison is invertible.
- Step 3: checked `lem-pur-supported-hom`'s natural identification and the kernel-of-restriction definition of support cohomology. The displayed transpose uses naturality of the compact-support exchange and preservation of composition, and proves that this specific mate acts by supported pullback. Verdict repaired; the non-elementary supported-Hom identification is cited rather than hidden inside an elementary step.
- Step 4: checked `prop-pur-gm-relative-kummer` clause (4), `thm-pur-with-support-exactness`'s pair/coefficient functoriality, and the global orientation/Gysin characterization. These give the displayed equality of supported boundaries with the same finite-level twist. Verdict repaired: `lem-pur-kummer-coefficient-base-change` gives coefficient extension on a fixed curve, not geometric pullback.
- Step 5: checked the explicit geometric-point clause of `prop-pur-gm-relative-kummer`, pair functoriality of support exactness, and the coordinate normalization in `thm-pur-rank-one-local-calculation`, including its pro-etale assertion. Verdict repaired: the point has an arbitrary algebraically closed field, not necessarily finite type over k, and no image residue field is silently substituted for it.
- Step 6: checked the global orientation normalization and the precise Hom-group injectivity of `prop-pur-affine-line-orientation-uniqueness` over Y'; verdict passes. The empty base has the zero Hom group, so the empty family causes no exception.
- New nodes: none. I searched the DAG across all chapters for supported pullback, Kummer naturality and exceptional comparisons; the two missing interfaces were already available, so no elementary lemma, duplicate, special case, or restatement was created. Independent Mathlib searches used the broader vocabulary of inverse image and localization boundary, and a grep for supportedRestriction/cohomologyWithSupport/exceptionalBaseChange; neither supplied a matching declaration. There are zero new Mathlib leaves.

Changes and reasons:

1. Replaced the restored single paragraph by six steps. The original fibre-normalization/uniqueness route is retained; support functoriality and the explicit mate calculation fill its two citation gaps. No localized-top-Chern or general purity theorem is used.
2. Removed `def-weil-exceptional-adjoint-admissibility` from proof dependencies: its statement specifies optional ambient admissibility and coefficient mates, not the geometric comparison claimed by the paragraph. Used the actual bounded etale-origin adjunction and compact-support exchange, with their hypotheses checked.
3. Removed the coefficient-only Kummer lemma from proof dependencies and used the existing relative Kummer theorem and support exactness. The coefficient lemma's own recorded citer audit already identifies this C4 mismatch.
4. Regenerated citations.json with one full verbatim current statement for every citation in every repaired step. Removed stale search verdict references to the previous six-step draft and recorded my actual searches.
5. Kept the first worker's report and `## Review by NV` above as requested; their claim that all seven original citations supply the necessary interfaces is superseded by this independent reading. No new statement, definition, target, unit route, or maintainer-owned field was changed.

Generic tools used outside the unit route are closed-immersion properness, the class-restricted exceptional adjunction, bounded constructible etale-origin witnesses, and compact-support exchange. They supply the comparison formalism for the original proof; they do not replace its Kummer/localization, geometric normalization or uniqueness steps. These are reported here for the maintainer's decision; no `tool_uses` approval metadata was added.

Small cases checked: identity v (identity exchange and mate), Y a field, Y' empty, two-component bases (sections are A^2, not a single copy of A), the dual-number base (the variable still pulls back to the variable), n=1 in the unramified finite-level datum, and the ramified allowed n=e case. No smoothness, regularity, reducedness, connectedness or flatness of Y or Y' enters the argument. Each added dependency was traversed through statement and proof dependencies and none reaches this item, so the repair creates no cycle.

Additional step 2 check: `lem-asd-etale-finite-twist-pullback` supplies the actual etale root/tensor pullback, and `lem-weil-pbc-comparison-pullback` supplies its pro-etale comparison. I wrote their composition with the affine-line datum's specified twist comparison, including the root-section formula and coefficient insertion; thus the proof uses the canonical fixed twist, not an unspecified rank-one identification. Both current statements were read in full and quoted in citations.json.
