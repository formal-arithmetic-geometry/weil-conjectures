## What changed

Completed all three theorem proofs in
`Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates`.
`directModel_existsUnique` specializes a proved private categorical helper:
exact postcomposition and precomposition by an additive equivalence give two
universal right derived pairs; `rightDerivedNatIso` compares them. Explicit
cochain computations identify the universal unit equation with the existing
`DirectModelNormalization`, and `rightDerived_ext` proves uniqueness.
`pullModelMap_isIso` and `openModelMap_isIso` follow from the adopted theorem
`isIso_mateEquiv_of_isEquivalence` on opposite adjunctions, using a proved
private helper for the inverse mate direction.

Added only private proof imports for the adopted derived-composition and mate
APIs. All existing public signatures, definition bodies, public imports,
attributes, options, universes and docstrings are preserved. No consumer needs
adaptation or semantic re-review. Updated the existing node's proof,
proof dependencies and proof origin to describe the implemented argument.
No new public interface or change record is needed.

The full module compiled cleanly through `lcompile.py` in 29.4 seconds before
adding the explicit direct mate import. Delivery performs the final compile
and axiom probe. The generic normalization helper also compiled independently.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to
`def-sf-integral-compactification-site-transport`:

- `WeilConjectures.IntegralCompactificationBridge.directModel_existsUnique`.
- `WeilConjectures.IntegralCompactificationBridge.pullModelMap_isIso`.
- `WeilConjectures.IntegralCompactificationBridge.openModelMap_isIso`.

Zero textual holes remain in the item; zero holes added; zero split off.
The ordinary section-normalized comparison and existing category/adjunction
infrastructure remain dependencies. Their outstanding proofs are not claimed
closed by this delivery. The chosen direct comparison is still selected from
its uniqueness theorem, which determines it up to equality.

## No longer needed

Removed the private proof imports
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` and
`Sheaf.SixFunctors.AmbientProperOpenPasting`: this coordinate construction uses
universal derivation and equivalence mates, without a limit comparison or
proper/open pasting. Neither module is withdrawn or claimed globally pruned;
other imports may still reach them. No stated dependency of the item node is
pruned. Existing public imports are retained as the published re-export API.
No node or module is withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's node had an empty proof plan. Its declaration docstrings correctly
suggest universal right derivation and equivalence transport; the updated node
now records the actual argument. No mathematical statement repair was needed.
The source library already proves both derived-composition instances and the
mate theorem; no new comparison obligation is needed. In the generic proof,
fully qualifying `CategoryTheory.Functor.map_id` and `map_comp` avoids resolving
those names to the unrelated root functor laws. Both adjunction-mate arguments
work for arbitrary schemes and include the empty open, since the only
invertibility hypotheses concern the site equivalences.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
