## What changed

Proved `AlgebraicGeometry.derived_lower_truncation_unit_bridge` in
`Sheaf.AlgebraicGeometry.DerivedLowerTruncationUnitBridge`, keeping its signature,
visibility, public imports and existing docstring unchanged. Added three proved
private helpers: `lowerTruncationLocalization`, `preservesBottomHomology`, and
`isIsoBottomUnit`. Only proof imports were added, for the source-library homology
truncation comparison, Mathlib CM5a, and preservation of short-complex homology.
Updated the original node's proof, proof_deps and proof_origin to the actual route.

The shortest route is a bounded-below injective replacement with the same lower
cutoff. Since bottom homology is a kernel, F preserves it; naturality of the actual
derived unit proves its bottom homology map invertible. The truncation comparison
is proved by its universal property and testing all homology degrees. Naturality
then proves the required equation, with its specified e, U and q.

## Proved and sorry left

Closed: `AlgebraicGeometry.derived_lower_truncation_unit_bridge`
(node `lem-sc-derived-lower-truncation-unit-bridge`), 1 of 1 original holes.
Added holes: none. Sorries left in the module or delivery: none.
All three private helpers have complete proofs. This is a proof, not a decomposition.
Single-file compilation passes with no warnings. The dry run probes the axioms.
No data is chosen from any unproved existence theorem: the injective replacement
and truncation universal property used here are proved library results.

## No longer needed

The old route's four proof dependencies are not used:

- `lem-weil-pbc-derived-functor-negative-vanishing`;
- `lem-weil-pbc-derived-direct-image-triangulated`;
- `lem-sp-derived-functor-single-identification`;
- `src-right-derived-functor-plus-compatibility`.

Their modules need no new direct imports:
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`,
and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
None was imported in the supplied module, so no original import was removed.
An exploratory direct import of Mathlib's HomotopyCategory.KInjective was removed
because the required theorem is already available from the existing imports.
The exploratory DerivedSectionsLeftExactBottom route and the two temporary
intermediate modules were removed from the delivery. There are no new public lemmas.
This does not claim any of these modules is unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No statement error or tool failure. The proposed route was longer than needed:
no normalized single-object comparison, shift argument, negative derived
vanishing or plus/unbounded compatibility is necessary. The existing proved
bottom isomorphism in DerivedSectionsLeftExactBottom alone does not identify the
actual derived unit, so it cannot directly supply the required factorization.
The actual unit is handled here by naturality along a proved injective replacement.

Searches: LeanFinder returned eight truncation/quasi-isomorphism hits, without
this normalized bridge; Loogle did not index rightDerivedFunctorUnit; msearch
and local rg found exists_quasiIso_injective, isKInjective_of_injective and
mapHomologyIso_hom_naturality. Their exact source signatures supplied the shorter
route. The unit record sk-thm-picard-duality has no realized node requiring the
old intermediate route. Arbitrary integer cutoffs, zero complexes, and unbounded
I are covered: only its good lower truncation must be strictly bounded below.

## Second reading by Y2

1. **Visibility and statements.** Compared the delivered module with the repository version. The public imports, theorem signature, visibility, and existing docstring of `AlgebraicGeometry.derived_lower_truncation_unit_bridge` are unchanged byte for byte. The three added helpers are private and do not alter the public interface. Verdict: pass.

2. **Proof and axioms.** Compiled `lean/Sheaf/AlgebraicGeometry/DerivedLowerTruncationUnitBridge.lean` with `lcompile.py`; it succeeds without warnings. Searched the module for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur. The proof uses only the existing derived-category, truncation, CM5a, and short-complex preservation APIs. Verdict: pass.

3. **Statements and split-offs.** No public statement was split off and no new node was added by this delivery. The private helpers are proved, with source and natural-language proof documentation. Their edge cases are covered uniformly for arbitrary integer cutoffs and zero complexes. Verdict: pass.

4. **Route and pruning.** The proof follows the unit route through the truncation/localization comparison and bottom derived-unit isomorphism, while removing an unnecessary negative-vanishing/single-object route. The node proof, proof dependencies, and proof origin match the actual Lean proof; the report's no-longer-needed list records the pruned route and imports. Verdict: pass.

5. **Delivery integrity.** The node and Lean declaration agree, and the module has no remaining holes. No definitions or target statements changed. Verdict: pass.

Changed only this report section; no repairs to the proof or node were needed.
