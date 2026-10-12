## What changed

Proved `AlgebraicGeometry.Scheme.exists_epi_coproduct_constructible` with its signature unchanged. Its family consists of rank-one constant module sheaves extended by zero from affine etale objects, indexed by pairs of an affine object and a morphism to the given sheaf. The proof applies the existing constructibility theorem to each summand, obtains coproducts from Mathlib's sheaf colimit instance, and proves the evaluation map epic using the separating family and the coproduct identities.

Added `Sheaf.AlgebraicGeometry.AffineEtaleRankOneSeparating`, with a complete proof of `AlgebraicGeometry.Scheme.affine_etale_rankOne_isSeparating`. This lemma is independent of compactness, quasi-separatedness and finite coefficients. Composing the constant-sheaf and lower-shriek adjunctions identifies morphisms from a summand with linear maps into sections. Rank-one linear maps detect equality on sections. The affine-etale cover-dense functor and Mathlib's injectivity of restriction of sheaf morphisms finish the proof. Empty schemes and the zero ring require no nonemptiness assumptions.

Added proof imports of the new helper module and `Mathlib.CategoryTheory.Sites.Limits`. Updated the target node's proof, proof dependencies and proof origin to describe this Lean argument. The unit's statement and realized steps are untouched: the affine-generator, constructibility and evaluation-coproduct argument is retained.

Both modules compile without warnings through `lcompile.py --all`. The new lemma's signature and its complete proof were compiled incrementally; no custom axioms or altered definitions were introduced.

## Proved and sorry left

Proved the item's one original sorry: `AlgebraicGeometry.Scheme.exists_epi_coproduct_constructible` (node `lem-weil-pbc-constructible-generation`).

Also proved `AlgebraicGeometry.Scheme.affine_etale_rankOne_isSeparating` (new node `lem-weil-pbc-affine-etale-rank-one-separating`).

No sorry remains in either delivered module, and no sorry was split off. The proof uses the existing imported theorem `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant`, whose sorry is not changed by this delivery (node `lem-weil-pbc-etale-free-sheaf-constructible`). This delivery closes the local proofs, not the transitive proof of constructibility.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The target argument no longer needs nodes `lem-weil-pbc-module-sheaves-grothendieck-abelian` or `lem-weil-pbc-module-sheaves-colimits-forgetful`: it works directly in `Sheaf X.smallEtaleTopology (ModuleCat Λ)`, where sheafification and Mathlib sheaf coproducts are available. Their ringed-site category comparison, ULift coefficient convention, and sheafified free-Yoneda generator construction are unnecessary for this proof. These modules may still be reached elsewhere or through other dependencies; no claim is made that they leave the entire target closure.

`lem-weil-pbc-affine-etale-essentially-small-cover` is moved from the target's direct dependencies to the separating-family lemma. Cover density remains used; selecting a skeleton or representatives is unnecessary because all affine etale objects already lie in the permitted index universe. The categorical epimorphism node `lem-weil-pbc-separating-family-epi-coproduct` remains realized by the explicit cancellation proof rather than by a separate application with a larger CostructuredArrow index.

No other original proof dependency was pruned. No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original generator dependency's Lean signature concerns `SheafOfModules` over a constant ring sheaf with ULift coefficients. The target and its constructibility dependency concern `Sheaf ... (ModuleCat Λ)` with coefficients in Type (u + 1). That generator theorem cannot directly supply the target's family without a comparison argument. The new proved lemma supplies exactly the affine separating-family step in the target category, without changing any existing statement.

The original module did not directly import the affine-cover or separating-family dependencies, which are Mathlib leaves; their APIs were read and used in the concrete proof. A generic attempt to infer an individual coproduct caused instance-search timeout; explicitly installing sheafification and `Sheaf.instHasColimitsOfSize` makes the compile fast without raising heartbeat limits or changing definitions.

LeanSearch returned Internal Server Error; the actual failure is recorded in `searches.jsonl`. LeanFinder, Loogle and Mathlib grep searches succeeded and were checked against declaration source.

## New nodes

`lem-weil-pbc-affine-etale-rank-one-separating`, at `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-rank-one-separating.json`, records the fully proved separating-family lemma in `lean/Sheaf/AlgebraicGeometry/AffineEtaleRankOneSeparating.lean`. It is strictly the affine generator portion of the original argument: it does not assert constructibility, existence of an epimorphism, or the target conclusion. It records the adjunction calculation, section detection and affine cover-density proof, with the source of the original step and real search records. No change record is needed because no existing definition or signature changed.

## Second reading by M1

1. Compared both delivered modules and the existing target module against the repository. Existing declaration signatures are unchanged; the new declaration is recorded by its node.
2. Compiled both modules with `lcompile.py --all`; compilation is clean. Searched the delivered files for forbidden `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and untracked `sorry`; none occur.
3. The split-off separating-family statement is true and strictly smaller than the target: it asserts only separation, with no constructibility or coproduct conclusion. Its docstring, node, source, and Lean signature agree, and searches found no existing duplicate.
4. The proof follows the unit route: affine rank-one generators, constructibility of each summand, then the explicit evaluation coproduct. Removed imports and pruned dependencies are listed above; no shorter applicable route was found.
5. The DAG proof, proof dependencies, proof origin, and realized unit route match the Lean proof. The target statement and definitions are unchanged.

Changed during second reading: no proof or statement changes were necessary; this section was added to satisfy the required review record.
