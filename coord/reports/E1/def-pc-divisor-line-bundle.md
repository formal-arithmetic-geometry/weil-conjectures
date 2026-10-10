# def-pc-divisor-line-bundle

## Files

- `dag/nodes/sec-picard-framework/def-pc-divisor-line-bundle.json`: definition split, no new nodes.

## Source and dependency check

Stacks Divisors, Definition 01WX (`definition-invertible-sheaf-effective-Cartier-divisor`, `/home/ubuntu/c1-stacks-review/divisors.tex:2658-2680`) defines the associated invertible sheaf as the internal Hom from the divisor's ideal sheaf to the structure sheaf. Definition 01WR (`definition-effective-Cartier-divisor`, lines 2384-2395) gives the general-scheme Cartier condition; Lemma 01WS gives the equivalent local non-zero-divisor criterion. The item's statement now spells out the latter condition rather than leaving "effective Cartier divisor" undefined. The existing `def-nagata-effective-cartier-ideal` gives the general local regular-generator notion; `def-sbc-closed-immersion-ideal-sheaf` defines the ideal sheaf of a closed subscheme on any scheme; `lemma-nagata-effective-cartier-is-invertible` states that the ideal sheaf is invertible; and `def-sc-invertible-module` defines the dual by internal Hom for any scheme. I removed `def-sc-divisor`, which defines formal sums on curves, and `def-sc-effective-cartier-divisor`, which is curve-only. The old `blueprint_uses` and `uses_not_cited` are retained as maintainer/import metadata per the fresh-base rule.

The source's cases behave as expected: for the empty Cartier divisor, the ideal is the unit sheaf and its dual is the unit sheaf; on an affine chart where the ideal is `(f)` with `f` a non-zero-divisor, multiplication by `f` identifies that ideal with the structure sheaf, and its dual is locally rank one. No assertion is made for a zero-divisor generator.

## Lean and Mathlib

No exact declaration for this definition was found by node tag or concept in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`. The sorry-free theorem `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` at `WeilConjectures/AlgebraicGeometry/EffectiveCartier.lean:200-209` is **partial**: it proves invertibility of `J.toModulesᵛ`, but does not define `O_X(D)`. The components `IdealSheafData.toModules` (`WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Module.lean:93`) and `Scheme.Modules.dual` (`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean:70-71`) are project declarations, not Mathlib. Thus there is no exact attachment for this item. The Mathlib search record is in the item.

The whole-DAG search for the definition and Stacks Tag 01WX, and `tools/blueprint_refs.py search` on the general-scheme concept, found no second blueprint node with this statement. `def-sc-divisor` gives a different construction on a curve. I set `blueprint.same_as` to `[]` and left `blueprint.is` as supplied by the maintainer.

## Checks and limits

The sandbox JSON parses. No new node or proof step was needed for a definition, so the new-node, citation, and proof-split checks B-D do not apply. The master blueprint file named by `source.document` is absent from this clone, but Stacks Definition 01WX is available in the separate source checkout above.

WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/def-pc-divisor-line-bundle.md` in this clone, to compare the imported node to its master blueprint source.

## Review by E1

I read the item and the four cited node statements against Stacks Divisors 01WR (`definition-effective-Cartier-divisor`), 01WS (`lemma-characterize-effective-Cartier-divisor`) and 01WX (`definition-invertible-sheaf-effective-Cartier-divisor`) in `divisors.tex`. Clause (1) of 01WX uses precisely a scheme `S`, an effective Cartier closed subscheme `D`, and its ideal sheaf, and defines `O_S(D)` as `Hom(I_D,O_S)`. By 01WS, the regular-generator condition in the edited statement is equivalent to 01WR's invertible-ideal definition, with no field hypothesis. `def-nagata-effective-cartier-ideal` states that condition on an arbitrary scheme; `def-sbc-closed-immersion-ideal-sheaf` supplies the kernel ideal sheaf of the closed immersion; `lemma-nagata-effective-cartier-is-invertible` states the needed invertibility; and `def-sc-invertible-module` supplies the internal-Hom dual. None of these statements depends on this item, and the item is a definition with no proof steps.

For B, there is no new node; the item retains its complete, source-faithful statement and uses a single TeX backslash after JSON decoding. For C and D, no non-elementary proof claim has been disguised as a definitional step, and the replacement dependencies were checked by reading their statements, not their proofs. For E, I checked the empty divisor and the local `(f)` chart with `f` regular: both yield an invertible ideal and hence a rank-one dual; a zero-divisor generator is excluded by 01WS. The imported curve-only Cartier node and the curve divisor node failed the source's general-scheme scope, so I removed those edges. A search across the DAG by Tag 01WX and the formula found no duplicate general-scheme definition. I made no change to the maintainer's `lean_audit` or `blueprint.is` mapping.

L's return B9 is resolved by the explicit `same_as: []`, after a whole-DAG search and `tools/blueprint_refs.py search` found no duplicate. Return B3 is resolved by spelling out "closed subscheme with locally regular-principal ideal sheaf" and citing the four nodes whose statements give each notion or invertibility; 01WS verifies equivalence with 01WR. For E7, that source-faithful wording change is named here. No new node or proof route was introduced.
