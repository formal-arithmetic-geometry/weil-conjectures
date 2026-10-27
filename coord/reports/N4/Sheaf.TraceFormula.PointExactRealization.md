## What changed

Proved `WeilConjectures.trfPointExactRealization` in
`lean/Sheaf/TraceFormula/PointExactRealization.lean`, with every declaration signature,
comparison definition and public import unchanged. Exactness uses the existing intrinsic
pullback and finite point sections instances. Quasi-isomorphism preservation is inferred
from exactness. The two derived-functor clauses specialize `exactFunctor_derivedFunctor`.
Residue-field units and `isomorphismFiniteDerivedPullback_termwise` prove constructibility;
the fibre inclusion equality is definitional. Updated the item's five DAG proof steps,
proof dependencies and proof origin to match this proof. The proof dependencies name
`def-sp-finite-intrinsic-pullback` for the intrinsic exactness instances and
`def-weil-point-section-scalar-functors` for additive finite sections.

The server single-file compile passed in 14.7 seconds with no warnings or errors.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.trfPointExactRealization`
(node `lem-trf-point-exact-realization`). Zero holes remain in the item; zero holes added;
zero split off. This is a proof from the published dependency declarations, including
any existing holes those declarations transitively use, not a claim that the whole
dependency closure is now axiom-free.

## No longer needed

Removed private imports `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`,
`Sheaf.Paper.PointProEtaleSectionsExact` and `Sheaf.Paper.PointSectionsFiniteness`.

Removed direct proof dependencies `prop-weil-pbc-proetale-constant-exact` and
`prop-weil-pbc-proetale-constant-ring-map`: the stated ordinary pullback is already the
published exact intrinsic realization, so no alternate presentation comparison is needed.
Removed direct proof dependency `lem-weil-point-proetale-sections-exact`: finite point
sections already exports exactness after scalar restriction. Removed
`lem-weil-point-sections-finiteness`: `pointFiniteFibre` already lands in the finite
cohomology subcategory and its inclusion equation is `rfl`. Removed
`def-weil-frobenius-detailed` as a direct proof dependency: point automorphism powers
and residue-field units are available from `def-weil-frobenius-point-transport`.
Removed the four corresponding obsolete top-level `tool_uses` approvals; retained
the exact-derived-functor and isomorphism-pullback approvals in their original order.
Replaced the direct dependency on the reexport node `def-weil-pbc-proetale-operations`
with the actual intrinsic-pullback owner `def-sp-finite-intrinsic-pullback`.
These facts may still be used transitively by existing declarations; no module is
withdrawn, and no global pruning of those modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan's direct coefficient-comparison and point-finiteness applications are
unnecessary at this interface: exactness and the restricted fibre have already been
constructed and published. The existing statement is unchanged and the unit route is
preserved. There were no tool failures or statement repairs.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
