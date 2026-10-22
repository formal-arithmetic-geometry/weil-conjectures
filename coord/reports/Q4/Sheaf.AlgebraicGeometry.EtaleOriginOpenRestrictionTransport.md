## What changed

Prove `AlgebraicGeometry.Scheme.etaleOriginOpenRestriction_transport` by pasting the
ordinary site-comparison mate cube with the canonical intrinsic-realization cube,
deriving the square, and applying the localized open-unit equation. The private
helpers check the normalization of every derived comparison. The private derived
coordinate definition is locally irreducible and used through its proved
factorization and K-injective formulas. Its concrete direct-image equations are
proved before rewriting the intrinsic cube, avoiding broad unfolding there. Public
statements, comparison definitions and public imports are unchanged.

The proof uses the library's generic mate-cube and right-derived-square machinery.
The ordinary mate cube is checked for a general chosen Cartesian square before
specializing to the displayed pullback. A private proposition structure, generic
over the coefficient category and its category, abelian and Grothendieck instances,
retains this equation through specialization. Its proved field supplies the
ordinary equation to the derived cube. This avoids the kernel's repeated comparison
of nested proof-instance arguments; a direct concrete specialization exceeded the
file limit. The canonical fixed-ring base-change map is identified with the open
restriction comparison in the general intrinsic cube. No public definition changes.
The ordinary open-unit calculation uses the source library's proved
`Adjunction.mapDerivedCategoryAdjunction_mate`.
For intrinsic open adjunctions, whose construction localizes complexes directly,
the unit equation is verified on homotopy images and extended by essential
surjectivity. The bounded-below direct-image comparison is identified using the
published inclusion comparisons.

The proof-context change record requested by preflight is
`coord/changes/Q4-etale-origin-open-restriction-proof-context.md`. It records the
local commands and all four downstream consumers; no consumer requires adaptation.

## Proved and sorry left

The proof body replaces the sole original hole,
`AlgebraicGeometry.Scheme.etaleOriginOpenRestriction_transport`. Holes closed: 1;
holes added: 0; holes remaining in the item: 0. No new statements are split off.
The complete module, including every private helper and the final theorem,
passed the server-only `lcompile.py` check in 42.6 seconds. The focused derived
cube check passed in 9.7 seconds, and both ordinary specializations passed in
about seven seconds. All eight added proof imports pass the project import-direction
check. `deliver3.py` performs the final compilation and preflight before pushing.
All added helpers are private and have complete proof bodies. Imported existing
proof obligations remain with their existing declarations.

## No longer needed

The direct proof import of
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` is removed:
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` (node
`lem-weil-pbc-transport-identifies-exchange`) is not used by this proof. The
ordinary mate cube and the exact derived-square cube give the needed square with
the stated normalization directly. No upstream declaration is removed or changed.

The direct import of
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` is removed. Its node
`lem-weil-pbc-comparison-pullback` is no longer a direct dependency: its
coherence enters through the proved `fixSiteOpenExchangeSquare` used here; this
module and node are therefore still needed transitively and are not withdrawn.

The redundant direct imports of
`Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, and
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` are also removed. Their interfaces
are available through the retained imports, and their declarations are still used;
these modules are not withdrawn.

No module is withdrawn. No unit-level route is removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG permitted use of the left-derived exchange comparison from
SmoothBaseChange. This proof instead uses the exact right-derived-square cube,
which fits the exact pullback presentation of the assigned theorem without
converting between those two derived presentations. The node's proof and
dependencies are updated accordingly. No mathematical statement is disputed.

The launcher currently attempts a local mirror, despite the brief's server-only
setup. The first delivery attempt stopped without pushing because that mirror
lacked `Mathlib.olean`. Subsequent checks select the supported server path with
`LCOMPILE_NO_LOCAL=1`. No launcher script was changed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
