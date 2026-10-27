## What changed

Proved `AlgebraicGeometry.Etale.properOpenRefinement_adjoint_projection` from the normalized
proper/open interchange and the K-injective counit formula. Private proved helpers construct
the sheaf projection as the ordinary adjoint, verify its section and disjoint-open formulas,
descend it through exact localization, and compare on K-injective resolutions.

Repaired the expensive representation of `unboundedProperOpenRefinementComparison`:
`ProperOpenRefinementData` retains only the two comparisons and their normalizations.
`nonempty_properOpenRefinementData` proves existence from the existing interchange, and
`properOpenRefinementData` selects the normalized data. Both maps are fixed by the formulas,
so this preserves the normalized mathematical comparison and its signature. The main theorem's
statement is unchanged. The node records this route and the supporting declarations.
The change record is `coord/changes/proper-open-refinement-normalized-data.md`.

Validation: the complete item and the byte-identical direct consumer
`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence` compiled together successfully
against the item overlay, with no compiler warnings. The consumer needs no adaptation
and is not part of this delivery. The original main theorem signature was compared verbatim.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.properOpenRefinement_adjoint_projection` (one original hole).
Added holes: none. Split off: none. Remaining holes in delivered modules: zero.
`AlgebraicGeometry.Etale.nonempty_properOpenRefinementData` and all private helpers are proved.
The proof uses the existing named dependency
`AlgebraicGeometry.Etale.derivedCounitKInjectiveTermwise`, whose existing hole is not changed.

## No longer needed

Removed the original private imports `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`,
`Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`,
`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
Added proof imports for the existing open-extension complement API and exact derived
restriction-composition API. The four public imports are preserved.

The proof does not use the explicit fibre-product construction, proper base-change instance,
`open_section_clopen`, `sheaf_clopen_product`, the extension-by-zero base-change map or its
isomorphism, or `properSupportSheafComposition` directly. The interchange supplies the
normalized sheaf comparison, and ordinary adjunction proves its two specified component
formulas. Proper-support composition remains used upstream and is not withdrawn.

The old proof-only dependencies removed from this node are `def-pc-fibre-product`,
`def-weil-pbc-etale-shriek-base-change-map`, `def-weil-proper-morphism`,
`lem-cbc-proper-support-sheaf-composition`, `lem-weil-pbc-etale-sheaf-clopen-product`,
`lem-weil-pbc-etale-shriek-base-change-modules`, `lem-weil-pbc-open-immersion-base-change`,
`lem-weil-pbc-open-section-clopen`, `lem-weil-pbc-proper-base-change`, and
`def-kun-unbounded-exchange`. Statement dependencies and other consumers retain their needs;
no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The explicit clopen sheaf-product dependency is
stated for abelian sheaves; it is unnecessary for the ModuleCat component formulas here.
The unit record has empty realized statement/steps, so this internal route change bypasses
no unit statement or mandated step. Empty U, identity p, an extra component over U, the
zero coefficient ring and unbounded complexes require no additional hypothesis.

The original public comparison definition alone took 37.5 seconds in an isolated compile,
with about 35 seconds in type checking; the original complete attempt exceeded 60 seconds.
Retaining normalized data in a structure repairs that representation within this module.
No source-library declaration or launcher tool is changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
