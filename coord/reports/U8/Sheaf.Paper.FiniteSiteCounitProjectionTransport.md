## What changed

Filled ten of the eleven theorem bodies in `Sheaf.Paper.FiniteSiteCounitProjectionTransport`,
without changing their statements or any existing public import. The proof uses the
already proved generic finite-ring helpers of the existing projection comparison and
finite compact projection modules via private `import all`. This avoids transporting the
coefficient ring through an additional universe lift. The completed transpose clauses use the existing compatible bounded Hom-chain calculation.
The normalized tensor-pair theorem remains the one original unfinished declaration.

The counit theorem obtains its dimension certificate from `c.g ≫ aY`. The diagram theorem
uses the actual generated diagram coherence equation. The exchange theorem uses the actual
compact-support exchange square, its arbitrary-origin invertibility theorem, and its witness
formula. Origin existence uses the proved fixed-module constructible comparison directly;
origin uniqueness and equality reflection use the fixed-module derived Hom bijection.
Updated the existing node's proof, dependencies and proof origin to describe this route.
No new modules, public statements, definitions, exported instances, or axioms are introduced.
The local proof attributes and downstream audit are documented in
`coord/changes/U8-finite-site-projection-proof-context.md`.

Searches: LeanFinder for bounded constructible/finite-Tor boundedness; Loogle for functor
fullness; launcher grep and direct source searches for projection comparison, bounded Hom
transposes, finite compact projection, origin reconstruction and diagram/exchange coherence.
The current blueprint `lem-pur-co-smooth-etale-locality.proof.md` Steps 1 and 3 and the
unit record `sk-thm-smooth-purity` were read; the unit route is preserved.

## Proved and sorry left

Ten existing holes closed, zero holes added, zero split off. The declarations are in
`AlgebraicGeometry.ProEtale`:

- `finiteSiteProjectionInput_plus_source`
- `finiteSiteProjectionInput_plus`
- `finiteSiteCounitProjectionTransport`
- `finiteSiteCounitAndTranspose`
- `finiteSiteProjections_isIso`
- `finiteSiteThetaTransport`
- `finiteSiteDiagramTransposes`
- `finiteSiteExchangeTransposes`
- `finiteSiteOriginIndependence`
- `finiteSiteConstructibleOrigin`

One original hole remains: `AlgebraicGeometry.ProEtale.finiteSiteTensorTranspose`.
Its original signature and sourced proof docstring are retained. No hole is added elsewhere.
A complete direct pair construction was elaborated in this session, but kernel checking
of that term repeatedly timed out while unfolding chosen derived-category localization
instances. Attempts using the existing normalized inverse projection square, generic
categorical cancellation, generic finite-ring specialization, cached proposition definitions,
and nested-instance proof sharing did not produce a kernel-checked proof within the
per-file limit. Those experiments are not imported or delivered. The remaining theorem
is left as its original named hole, rather than replaced by a split or changed statement.
Existing dependencies retain their own proof obligations. Compilation and delivery preflight
are recorded by the delivery tool.

## No longer needed

Removed unused private imports:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`: the fixed-module comparison theorem already
  matches the intrinsic input and yields the needed origin, without encoding conversion.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: the proved projection-square helper
  already contains the tensor/pullback comparison calculation.
- `Sheaf.Paper.RingedExchangeTensorCoherence`: the existing projection-square helper and
  compact-support exchange theorem already contain those calculations.
- `Mathlib.CategoryTheory.Adjunction.Mates`: no direct mate-pasting theorem is needed in this
  assembly; the existing bounded Hom-chain and generated diagram theorems suffice.

The changed route no longer uses these planned dependencies as separate assembly steps:
`lem-pur-bounded-site-tensor-transposes`, `lem-pur-bounded-site-compositor-conjugates`,
`lem-pur-bounded-site-exchange-transposes`, and `lem-sf-proetale-constructible-origin`.
The remaining tensor-pair proof has a direct inverse-projection plan; the theta statement is the
existing Hom-chain compatibility applied to the inverse etale adjunct, the compositor and
exchange clauses follow from the actual diagram/exchange equations, and origin existence
is already proved by `new-etale-proetale-exceptional-object-comparison`.
`thm-weil-pbc-site-comparison` is replaced in the equality/lifting assembly step by the exact
recorded Hom-bijection node `lem-weil-pbc-fixed-module-derived-hom-bijection`.
`def-sf-compact-support-site-comparison-construction` remains needed by the statements and
existing square, but is not an additional proof step. No module is withdrawn: these nodes
may have other consumers, and public imports and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's extracted tensor/compositor/exchange theorem families impose additional
intermediate boundedness and adjunction data that the present statements do not need.
They are unnecessary for this assembly because the exact normalized generic projection
square, bounded transpose compatibility, generated diagram coherence and arbitrary-base-change
exchange comparison are already proved. The public finite-coefficient projection theorem
uses a coefficient-extension type in a different universe presentation, while its proved
generic helpers accept the actual lifted ring directly. Reusing those helpers avoids a
new scalar comparison interface. No statement is changed or disputed.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
