## What changed

Closed both holes of `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`
using the existing declarations named by its DAG plan. The finite intermediate field
gets the norm induced by its algebraic-closure embedding and the resulting normed
Q_ell-algebra structure. Continuous integral scalar extension is exact, so the generic
exact scalar-extension theorem proves preservation of bounded constructibility.

For localization, the canonical left-derived/termwise comparison transports the shift
and triangulated structure to the actual specified left derived extension. The existing
proved private `CategoryTheory.rationalization_of_subcategory_models` is then applied
to the original restricted functor and compatibility isomorphism. Its four premises are
supplied by `continuousConstructible_integral_model`, `derived_nsmul_isIso`,
`continuousConstructible_clear_denominators`, and the existing proved private
`integral_scalar_map_eq`. This follows the node's current proof steps, including the
unit's preservation, restricted-extension, localization and equivalence route.

Added six private proof imports and local irreducibility attributes only. The existing
public imports, signatures, attributes and non-theorem bodies remain unchanged. The
preserved helper archive is imported with `import all`; its proofs are reused unchanged.
The current import graph permits this without any consumer edit. The consumer audit
and scope explanation are in
`coord/changes/T8-ell-adic-rationalization-proofs.md`.

Validation: the complete item compiled with no warnings via lcompile.py (25.7 seconds).
An initial delivery compile exceeded 60 seconds and pushed nothing. Profiling identified
repeated inference of `F.leftDerivedFunctor` as a hotspot. The localization proof now
caches the actual derived and termwise functors in local lets and applies the criterion
with all four premises at once. No definition or mathematical proof route changes.
No profiling options remain. The delivery tool performs its own compilation and
declaration/axiom checks.

## Proved and sorry left

Holes closed: 2 of 2.

- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj`
  (`lem-sfb-extend-scalars-bounded-constructible`).
- `AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
  (`thm-sfb-extend-scalars-localization`).

Holes added: zero. Split-off statements: zero. No sorry remains in the item.
Existing dependencies may still rest on unresolved theorems; no claim is made that
the entire target closure is axiom-free. No definitions acquire holes.

## No longer needed

None. Every added private import supplies a theorem, instance or proved private helper
used by these proofs. No original public import was removed. All existing DAG
proof dependencies are retained, including those used transitively by the archived
helpers. No declaration, node or module is withdrawn. The implementation follows the
current DAG proof plan, so no node route update is needed.

## Where the brief, the DAG or earlier work was wrong

Historical review metadata records zero holes from the G1 landing, but the current
source again contains two holes after upstream synchronization. Its current DAG plans
and preserved proved helpers still apply directly. Unlike the earlier G1 delivery,
the current dependency graph no longer requires an import-cycle repair in
CompletedCondensedCoefficients. No shared repository or launcher file was edited.
The source module's historical Sorried input prose is retained under the source-library
boundary; the actual two bodies are now complete.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
