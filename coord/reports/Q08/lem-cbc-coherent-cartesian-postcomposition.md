# Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-coherent-square-comparison-data.json` — one new unsplit statement node; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-cbc-coherent-cartesian-postcomposition.json` — repaired four-step proof; statement and hypotheses unchanged.
- `citations.json` — verbatim quotations for every cited node used by every item step.
- `searches.jsonl` — retained search log, with the new comparison-data searches run through `msearch.py`.

Attachments: none. I searched the read-only slopmaster2 source for the item id, its blueprint tag, and the relevant Cartesian/coherent-realization declarations. No sorry-free declaration states the item exactly.

WANTED: archival copies of HTT Theorem 2.2.5.1 and Proposition 2.4.4.3, and Kerodon 03N2/046J/03PD, for the coherent replacement and Hom-functor interfaces. No SGA source is used.

## Not duplicates

- `lem-cbc-coherent-square-comparison-data` vs `lem-coef-infinity-hom-bifunctor-functoriality`: the existing node gives global coherent Hom bifunctors and functorial transformations; the new node specializes that interface to the four replacement/mapping squares and records the four witnesses and the relative-endpoint boundary-path homotopy. It asserts no pullback property.
- `lem-cbc-coherent-square-comparison-data` vs `lem-coef-space-transport-classification`: the existing node classifies transport by a coherent Hom bifunctor and arrow fibration over an arbitrary base; the new node fixes one Cartesian postcomposition square and adds locally Kan replacement/coherent-nerve corner maps plus its explicit cube boundary witnesses.
- `lem-cbc-coherent-square-comparison-data` vs `lem-coef-infinity-relative-hom-evaluation`: the existing node evaluates a parameterized Hom transformation over a simplicial base and makes no Kan-replacement comparison; the new node compares the four replacement squares and records the relative-endpoint boundary-path homotopy needed for cube invariance.
- `lem-cbc-coherent-square-comparison-data` vs `lem-coef-infinity-kan-homotopy-coherent-cube-invariance`: the existing node transfers a homotopy pullback across already supplied cubes; the new node constructs the comparison data and makes no transfer assertion.
- `lem-cbc-coherent-cartesian-postcomposition` vs `lem-coef-infinity-cartesian-mapping-criterion`: the existing criterion is a square of right-pinched quasicategorical mapping spaces; the item is the corresponding enriched square of coherent-realization mapping simplicial sets, whose unreplaced corners need not be Kan.
- `lem-cbc-coherent-cartesian-postcomposition` vs `lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence`: that node assumes a cartesian fibration over a standard simplex and concludes a single weak equivalence; the item treats an arbitrary inner fibration and proves a four-corner homotopy pullback square.

## What was wrong and what changed

The returned proof's Step 2 promoted the homotopy-category clause of `lem-coef-rigidification-postcomposition-comparison` to strict commutation. That clause only says that postcomposition is carried to enriched postcomposition after interpreting an inverse comparison in the homotopy category. The proof therefore did not supply the strict square required by strict homotopy-cartesian invariance. Its Step 3 then asserted a coherent cube without naming the four side witnesses or proving that the two boundary paths agree up to a relative-endpoint homotopy.

I added `lem-cbc-coherent-square-comparison-data` as a strictly smaller interface. It records the actual functorial locally Kan replacements, the four corner weak equivalences, the side homotopies `L,M,N,O`, the commutation homotopies `H,H'`, and the explicit two boundary paths together with their relative-endpoint homotopy. Its proof obtains these witnesses from the higher simplices of the coherent Hom natural transformations and the natural coherent-nerve comparisons. The item now applies coherent-cube invariance only after citing that data. Step 4 remains the conditional strict replacement-map transfer, and its strict commutation is justified directly by enriched functoriality.

## What I could not finish

No Lean was written or compiled, as required for this stage. The archival HTT and Kerodon sources are not present locally; their locations and exact places are recorded above and in the node sources.

## Review by Q08

I reread the returned item, the complete `sk-prop-sf-cbc` unit record, the 1089-byte ancestor proof `thm-cbc-finite-level-proetale.proof.md`, and the full statements of every cited node. The item's statement is unchanged: it still assumes only an inner fibration of small quasicategories, a `p`-Cartesian edge, and an arbitrary vertex, and it still concludes the displayed strictly commutative coherent-realization square is a path-space homotopy pullback. I checked the empty mapping-space case, the identity-fibration case, degenerate edges, and the terminal base; none adds a hypothesis or changes the conclusion.

For Step 1, `lem-coef-infinity-cartesian-mapping-criterion` explicitly gives the right-pinched mapping-space square and defines its homotopy-pullback comparison by the path-space homotopy fiber product. The step uses exactly its inner-fibration and Cartesian-edge hypotheses, with no assumption that other Cartesian lifts exist.

For the new comparison-data node, I read its source interfaces and checked each proof step. Step 1 uses the functorial object-preserving locally Kan replacement, its weak equivalences on every mapping set, and the natural coherent-nerve mapping comparisons from `lem-coef-coherent-nerve-comparison`; the rigidification node supplies the weak equivalences on the right-pinched mapping spaces. Step 2 uses the statement of `lem-coef-infinity-hom-bifunctor-functoriality`, which retains higher simplices and preserves canonical composition, together with the mapping-composition interface. It names the four side homotopies and the two paths in the same order as the cube criterion, and the higher naturality simplex supplies the relative-endpoint homotopy. Step 3 checks strict commutation only for the enriched replacement square, where `R p` is an actual simplicial functor, and uses naturality of the coherent-nerve comparisons for the remaining side faces. The new node asserts comparison data only, so it is strictly smaller than the item and does not package the item's pullback conclusion.

For Step 2 of the item, I checked that the new node supplies weak equivalences on all four corners and explicitly supplies `L,M,N,O`, `H,H'`, and the two boundary paths. The cited `lem-coef-infinity-kan-homotopy-coherent-cube-invariance` applies precisely to a coherent cube with those witnesses, so the transfer from the Step 1 right-pinched square to the coherent-nerve square is conditional on stated data rather than inferred from a homotopy-category equality. For Step 3, the same node supplies the locally Kan enriched square, whose commutation is strict, and the coherent side witnesses to the coherent-nerve square; both sides are Kan, so the same cube criterion transfers homotopy cartesianness. For Step 4, the replacement maps are actual enriched functors and hence commute strictly with vertical and postcomposition maps; `lem-coef-coherent-nerve-comparison` supplies weak equivalences on all mapping sets, and `lem-coef-kan-homotopy-cartesian-invariance` supplies the final transfer back to the unreplaced square.

I checked every citation quote in `citations.json` against the cited node's statement, checked that `proof_deps` is exactly the union of the item step uses, and checked all Mathlib searches for the new node. The new node is statement-only, as required for an unsplit dependency; its interface statement records the exact witnesses the item takes from it. It is not a duplicate of the global Hom-functor, cube-invariance, or Cartesian mapping criteria for the reasons listed above. Every item proof step is below the 2000-character long-step threshold. The only changed files are the item, the new node, `citations.json`, this report, and the retained search log.
