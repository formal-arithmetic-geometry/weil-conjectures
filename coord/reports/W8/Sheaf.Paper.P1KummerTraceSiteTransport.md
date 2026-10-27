## What changed

Filled `AlgebraicGeometry.ProEtale.VectorIntegrationSite.p1KummerTraceSiteTransport`
in `lean/Sheaf/Paper/P1KummerTraceSiteTransport.lean`, retaining its statement,
all existing definitions, and all public imports. No other Lean module is changed.

The pre-adjunction Chern equation uses the existing
`supportedProjectiveChern_comparison` declaration (node
`lem-pur-supported-projective-chern-comparison`), added to the shared library while
this item was in progress. Private proved helpers transport this equation through
adjunction, compare both biproduct components, invert the decomposition, and identify
the prescribed trace. Naturality then proves the affine-chart equation.

For arbitrary unbounded complexes, the existing derived open-unit normalization
and the adjunction triangle identities give the exact open-counit equation, including
the stated source comparisons. All proof imports are private.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.p1KummerTraceSiteTransport`
(blueprint: `lem-pur-p1-kummer-trace-site-transport`).
Zero holes remain in the item. Zero holes are added; zero statements are split off.
Every private helper is proved. The proof uses existing declarations that remain
unfinished, as the stage-3 brief permits.

Validation: the clean module compiled with `lcompile.py` in 57.5 seconds, with no
warnings. The delivery runs the remaining consumer, node, signature, and axiom checks.

## No longer needed

No original public import or module is withdrawn, and no adopted source declaration
is changed. The unit route through the normalized ordinary projective-line datum,
its decomposition, and its second-summand trace is preserved.

This file does not need separate imports of ordinary finite-class comparison,
adic root-comparison uniqueness, the projective coordinate-section charts, affine
zero sections, or ideal-sheaf functoriality. The existing supported Chern-comparison
node owns that calculation; its dependencies remain there. The item no longer lists
`lem-amb-cartier-kummer-map`, `lem-amb-finite-tate-site-descent`,
`lem-asd-ordinary-finite-class-comparison`, `def-pur-adic-root-comparisons`, or
`def-asd-ordinary-finite-p1-kummer-class` as direct proof dependencies.

The separate `lem-pur-mate-unit-compatibility` statement is unnecessary:
`Adjunction.homEquiv_unit` and naturality give the first component directly.
Its obsolete tool-use entry is removed from this node; no other approval is changed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The shared library gained the precise
pre-adjunction Chern-comparison statement during this session, so its divisor and
Ext calculations are reused rather than repeated. The node now records this input
and the actual adjunction, biproduct, trace, and unbounded open-counit arguments.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
