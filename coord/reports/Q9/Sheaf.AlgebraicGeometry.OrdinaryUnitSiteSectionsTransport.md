## What changed

Filled the five theorem proofs in `Sheaf.AlgebraicGeometry.OrdinaryUnitSiteSectionsTransport`.
All fourteen existing declaration signatures and all nine concrete definitions are unchanged.
Only this Lean module and its proof-route node are changed. Private, proved helpers establish
terminal-section evaluation, the unit/mate equation, normalized right-derived base-change
naturality and pasting, and preservation of lower cohomological bounds.

The fixed-scalar model already used by the public definitions permits a direct proof:
the adjunction mate calculation transports the unit; uniqueness of right-derived transformations
proves the unit/Leray and pasting identities; the underived square follows from the composite
adjunction unit and naturality at the terminal objects. The proof specializes these identities
to the named canonical maps rather than replacing them by arbitrary isomorphisms.
The negative-degree assertion uses exactness and the existing right-derived lower-bound theorem.

Added a private proof import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
The normalized-unit argument adapts existing private calculations from
`SupportSiteComparison`, without importing its unrelated support theory.
No existing statement or definition is repaired, and no consumer adaptation is needed.

## Proved and sorry left

Closed the five original holes, all in namespace `AlgebraicGeometry.ProEtale`:

- `ordinaryUnitSiteTransport`.
- `ordinaryUnitSiteTransport_isIso`.
- `ordinaryUnitSiteSections_comparison`.
- `ordinaryUnitSiteSections_unit_leray`.
- `ordinaryUnitSiteSections_negative`.

There are zero remaining holes in this module and zero holes added anywhere. No statements
are split off. The canonical comparison and mate declarations remain dependencies of the
proof; their proofs are outside this item. This delivery closes five local holes, rather
than making a separate claim about the full transitive axiom closure.

## No longer needed

Removed the plain imports `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` and
`Mathlib.CategoryTheory.Adjunction.Mates` (the latter is already available transitively).
The proof does not use `prop-weil-pbc-proetale-constant-ring-map`, so its obsolete `tool_uses`
entry and proof dependency are removed from this node.

The planned dependency `lem-pur-site-derived-sections-unit-pasting`, module
`Sheaf.CategoryTheory.Sites.DerivedSectionsUnitPasting`, is unnecessary for this item:
the public maps already use fixed-scalar sheaves, and their required normalization, pasting,
and unit/Leray equations are proved directly here. That module is not imported.
No other node or module is withdrawn. Other consumers may still need these two dependencies;
this report claims only that the present proof does not.

## Where the brief, the DAG or earlier work was wrong

The planned route through the intrinsic coefficient-module pasting theorem is longer than
needed for the existing fixed-scalar definitions. The node proof and proof dependencies now
record the direct adjunction and derived-uniqueness argument. Existing declaration docstrings
retain the historical planned explanation; the actual proof route is recorded here and in
the updated node. The unit's own statement and realized route are preserved.

The source-library sync during this session removed `PlusBaseChangeNaturality` and two
homotopy whiskering helper names. Their import and references are replaced by direct local
calculations; no adopted source-library module is edited or restored.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
