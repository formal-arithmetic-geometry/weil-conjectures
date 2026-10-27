## What changed

Replaced the proof hole in `Sheaf.AlgebraicGeometry.CartierReductionPullback` by a
construction of one simultaneous roots-normalized twist transport and a proof from
ordinary supported Kummer pullback, finite base change, and the sheaf-level
comparison of closed exchanges. The two proved private Ext lemmas implement
naturality under a square of exact functors and cancellation of the supported-source
isomorphisms. The theorem signature and its public import are unchanged.

Validation: remote single-file compilation passed for the new module in 42.9 seconds
and the assigned module in 51.7 seconds, without errors. Every node dependency resolves,
the original theorem signature is preserved verbatim, and all Lean lines meet the
100-character limit.

Added `Sheaf.AlgebraicGeometry.CartierClosedExchangeComparison`, containing only the
remaining equality of sheaf maps. It has no Kummer class, Cartier-ideal, annihilator,
finite-ring, or Ext hypothesis/conclusion. Its node gives the adjunction/counit proof
and its exact statement. This is a strictly smaller comparison-coherence step, not a
renaming of the assigned theorem. No existing shared module or definition changes.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_pullback`
(`lem-sfb-cartier-reduction-pullback`). No `sorry` remains in the assigned module.
The ordinary Kummer pullback theorem is used with the actual two canonical ordinary
boundary classes and their boundary specifications, and the canonical pro-etale
exchange is proved invertible via the comparison square and finite base change.

Added one hole:
`AlgebraicGeometry.ProEtale.geoCartier_closed_exchange_comparison`
(`lem-sfb-cartier-closed-exchange-comparison`). This is one decomposition: one upper
hole closed and one strictly smaller sheaf-map equality added, with net textual hole
change zero. Existing imported holes are not claimed as proved. There are no hollow
definitions and no chosen data from a mere unproved existence statement: the twist
transport is explicitly assembled from its normalized roots and line components.

## No longer needed

No existing public import is removed, and no module is withdrawn. The following old
direct proof dependencies are no longer used directly by this module:

- `def-sp-cartier-pole-boundary` / `Sheaf.AlgebraicGeometry.CartierPoleBoundary` and
  `def-pc-divisor-line-bundle` / `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  the pole-boundary and Cartier arguments are supplied by the already stated ordinary
  supported Kummer pullback theorem.
- `lemma-weil-pbc-finite-stalk-formula` /
  `WeilConjectures.SixFunctors.Finite.Stalk` and
  `lemma-weil-pbc-geometric-stalk-conservative` /
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`: the proof uses the
  already proved finite base-change theorem instead of repeating its stalk argument.
- `lem-asd-ordinary-supported-kummer` /
  `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`: its canonical boundary
  construction remains available through the unchanged statement import; the proof
  uses its specific pullback theorem and the canonical boundary specifications.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` /
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: all classes here are module-sheaf
  Ext classes, so exact-functor Ext naturality suffices.
- `sk-thm-pe-direct-image-comparison` /
  `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: the required closed-source
  comparison is already the specified isomorphism in `GeoCartierSourceComparison`;
  no separate derived direct-image comparison theorem is needed.

These are direct-edge simplifications only. Some remain transitive dependencies of
other declarations or of the preserved statement import, so this packet claims no
whole-module pruning. The unit route is retained: construct the ordinary boundary,
then apply exact site comparison and its actual source mate.

## Where the brief, the DAG or earlier work was wrong

The old plan's final sentence hid the equality identifying the specified comparison
exchange with the actual pro-etale counit mate. No existing declaration found states
that exact equality. It is isolated at the sheaf level, before any Kummer class or
Ext calculation. Its edge cases (identity arrows, empty schemes, zero coefficient
ring) obey the same adjunction identity; no flatness hypothesis is introduced.

The remainder of the old plan is implemented using the existing declarations rather
than reproving their still-open geometric arguments. The original theorem is not
weakened. Mathlib searches used LeanSearch, LeanFinder, Loogle and source grep;
Mathlib supplies generic exact-functor Ext tools, but no specialized Cartier exchange
comparison. The existing private exact-functor-square argument in
`QcoherentExactComparisonPullback` was read and reused as a private proof here.

## New nodes

`lem-sfb-cartier-closed-exchange-comparison`, in the assigned node's chapter and unit,
records equality between pullback of the source comparison followed by pro-etale
exchange and the site inverse-image comparison followed by comparison of ordinary
exchange and the primed source comparison. It is a statement solely about ordinary
sheaf maps. Its source is the opening and final naturality paragraphs of the current
blueprint's Cartier proof. The proof in words expands the mate, uses the counit and
inverse-image composition laws, moves the normalized constant map by naturality,
and cancels the adjunction equivalence. No change record is needed because no
existing interface, definition, public import, or consumer is changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
