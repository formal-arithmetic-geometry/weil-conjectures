## What changed

Completed both remaining proofs in `Sheaf.WeilSheaf.NativeOpenProperForgetting`.
`compactificationComparison_commShift` applies the four proved generic shift
helpers of `Sheaf.CategoryTheory.CompactSupportIdentityCalculus`, then assembles
associators and exact open forgetting. A private `import all` exposes those
private proved helpers; no public declaration uses them in its type or definition.
`compactificationComparison_frobenius` specializes
`NativeWeilInduction.nativeWeil_comparison_structure`: the native comparison,
ordinary exchange, ordinary compact supports and localized structure agree
with the existing constructions by definitional equality.

Added only these two proof imports. Existing signatures, definitions, public
imports and attributes are preserved. Updated the main node and its two component
nodes in their proof, proof_deps and proof_origin fields to match the proofs.
No other existing module is changed; no change record is required.

## Proved and sorry left

Closed 2 of the item's 2 holes:

- `AlgebraicGeometry.NativeWeilOpenProper.compactificationComparison_commShift`
  (`lem-sf-native-weil-open-proper-forgetting-comm-shift`).
- `AlgebraicGeometry.NativeWeilOpenProper.compactificationComparison_frobenius`
  (`lem-sf-native-weil-open-proper-forgetting-frobenius`).

Holes added: 0. Split off: 0. Sorries left in the delivered module: 0.
The existing `open_proper` assembly now uses these completed component proofs.
The proof compile completed in 33.2 seconds; its two linter warnings were then
removed without changing any statement or proof argument. Delivery runs the
final clean compilation and axiom checks.

## No longer needed

No imports or modules are withdrawn. No whole-module pruning is claimed.
The main node no longer directly requires
`lem-sfb-grothendieck-k-injective` or
`lem-weil-pbc-kinjective-hom-derived` for its final assembly: the two proved
components and naturality suffice. These nodes may remain needed by other
proofs and by imported comparison implementations; they are not withdrawn.
The Frobenius component replaces its old direct proof dependencies
`def-sf-native-weil-derived-framework`, `def-sfb-right-derived-functor`,
`lem-sf-exact-functor-derived-triangulated` and
`lem-weil-pbc-kinjective-exact-square-comparison` by the existing proved
`lem-sf-native-weil-comparison-structure`.
The shift component uses the existing proved generic shift helpers and exact
localization, so its old direct dependencies `def-sfb-right-derived-functor`
and `lem-weil-pbc-kinjective-exact-square-comparison` are unnecessary there.
These are removals of direct DAG edges, not claims of globally unused theory.

## Where the brief, the DAG or earlier work was wrong

The old Frobenius proof plan was mathematically appropriate, but the full
compatibility equation was already proved in NativeWeilComparisonStructure.
The constructions agree without changing any coefficient realization or action.
Likewise, the generic shift calculations already exist as proved private helpers.
Recorded LeanFinder, Loogle and Mathlib grep searches found generic shift APIs;
local source search found the stronger project-specific results used here.
The unit route is preserved; the unit's realized statement/steps lists are empty,
and these proofs implement the stated open/proper assembly.

The current queue row is a stage-3 proof assignment with two holes, not a
zero-hole rework assignment. The saved 2026-10-26 build error records failed
imports; the current module imports successfully in the server proof compiles.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeOpenProperForgetting": "a72bd67b6dddb9e9ddd2d9117056ef4440b4ae80"}, "results": {}, "time": "2026-10-28T12:02:53+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
