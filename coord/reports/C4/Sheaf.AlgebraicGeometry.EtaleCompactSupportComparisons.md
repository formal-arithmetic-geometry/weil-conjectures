## What changed

Proved `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq` by applying
`compactSupportFiniteTorsion` to the identity Cartesian base-change square. Its second conjunct
already states the required proper/open normalization for arbitrary refinements. The existing
upstream comparison equalities identify its canonical comparison with the requested refinement
isomorphism.

Added the proof-only import `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion` and removed
the unused proof imports listed below. All four public imports and the original theorem
signature are unchanged. Updated the existing node's proof, proof dependencies and proof origin.
No definition or other module is changed.

The direct definitional conversion exceeded the single-file limit. Profiling and isolated
conversion tests located the expensive operation in computing the formalism's pushforward
compositor. Rewriting with the existing proved `derivedPlusFormalism_pfComp'_inv` before
comparing the morphisms fixes that cost. No timeout or heartbeat limit is raised. The complete
proof compiled against the original published dependency in 9.7 seconds, with no warnings.
The final module, after removing all experimental overlay artifacts, compiled in 5.9 seconds.
An experimental dependency repair was discarded; its source and compiled sandbox artifacts
were removed before the final compile.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`
(node `lem-amb-etale-compact-comparisons`). Added 0 holes. The delivered module has 0 sorries.
There are no new intermediate theorems, nodes, axioms or definitions.

This is a proof from existing stated declarations, as required in stage 3. In particular,
`AlgebraicGeometry.Etale.compactSupportFiniteTorsion` (node `thm-cbc-finite-torsion`) remains
an existing theorem with `sorry` outside this delivery; its underlying obligation is not
claimed as solved. Nothing is split off or moved to a new hole.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.CompactificationCategory`
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonIso`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Replaced the original node's following direct proof dependencies by
`thm-cbc-finite-torsion` and `lem-weil-pbc-etale-shriek-compactification-independence`:

- `pqf-def-locnoeth`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `def-weil-proper-morphism`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-direct-image-preserves-injectives`
- `def-pc-fibre-product`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-proper-open-comparison-iso`
- `lem-weil-pbc-proper-open-comparison-composition`
- `def-weil-pbc-proper-open-comparison`
- `prop-nagata-compactification-category`
- `lem-weil-pbc-compatible-compactification-triangle`
- `def-amb-etale-compact-support`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-cbc-extension-zero-composition`
- `lem-cbc-compactifiable-compatible-tower`

The reused finite-torsion theorem already contains the normalization, and the unchanged public
upstream imports already supply the rest of the node's comparison/composition package. Thus
this module need not reconstruct geometry of compactifications, injective resolutions,
proper/open invertibility/transitivity, compatible towers, or interchange pasting. Their
occurrences as dependencies of the reused theorem or elsewhere in the project remain needed;
these removals do not assert that those modules are globally unreachable. No module is withdrawn.
The public statement imports remain necessary and are retained.

## Where the brief, the DAG or earlier work was wrong

The node planned reconstructing the whole comparison/composition package, although its Lean
record already attaches that package to existing upstream declarations. The module's only
missing equation is also the normalization clause of the more general existing
`compactSupportFiniteTorsion` theorem. Reusing that clause is a shorter route below the unit
level. No mathematical statement is changed or disputed.

The import-direction check allows the new import. A full dependency traversal found no reverse
DAG path from `thm-cbc-finite-torsion` to this item. Both belong to `sk-prop-sf-cbc`, whose
`realized` statement and step lists are empty; this proof changes no unit statement or realized
unit step. The current blueprint unit and comparison proof, and Stacks Tag 0F7I
(`lemma-shriek-well-defined`), were read.

Searches performed with the prescribed msearch wrapper: LeanFinder for canonical
compactification refinement versus proper/open comparison (8 unrelated Mathlib hits), Loogle
for `"RefinementIso"` (0 hits), and grep for
`refinementOpenImmersionLowerShriek|properOpenIdentification` (0 indexed hits). Direct source
search found the existing finite-torsion normalization and all upstream comparison identities.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
