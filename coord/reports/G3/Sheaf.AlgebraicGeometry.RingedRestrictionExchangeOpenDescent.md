## What changed

Reduced `open_sectionwise` in
`Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent` to the ordinary
unit-normalization identification in the new import
`Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization`.

The existing `proEtaleOpenRestrictionCounit` supplies beta, its complete section
formula, alpha, alpha's unit normalization and the counit equation. The new proved
private helper `open_alpha_unique` uses injectivity of the composite adjunction's
Hom equivalence: equal unit normalizations give equal transposes on every section.
The item then identifies alpha with the inverse selected module square and applies
the new proved private generic lemma `mate_eq_of_counit`. This lemma uses
injectivity of the target adjunction's inverse Hom equivalence and cancels alpha.
The counit equation and `mateEquiv_counit` identify beta with the native mate.
A separate proved reflexive equality identifies that native mate with `ordinary`;
keeping these steps separate avoids expensive coefficient-record conversions.
The statement, coefficients and section formula are unchanged.

To avoid kernel conversion of independently expanded coefficient records, the
existing `cartesian`, `actualCoefficients_coherent` and `actualSquare` declarations
move verbatim into the new normalization module, together with their private
coherence helpers. The item publicly imports that module and re-exports the same
declarations. Their signatures, data and meaning stay identical. The original
identity-coherence proof retains its private identity helpers. The move is recorded
in `coord/changes/ringed-open-square-shared-coefficients.md`. A direct-import scan
found no downstream importers of the item; no other existing Lean module changes.

The one remaining normalization step is in a new module with a node, a source,
and a complete proof in words. It concerns only the inverse-image compositor's
unit equation. It has no beta, exchange mate, derived category, K-injective
complex or resolution. No data is chosen from this theorem.

Validation: `lcompile.py --all` compiled the complete final packet, with the new
normalization module in 3.7 seconds and the item in 49.1 seconds, within the
60-second per-file limit. All profiler settings and temporary test files were
removed. The generic counit proof and native-mate identification were also checked
in isolation before integration. Every Lean line has at most 100 characters.

## Proved and sorry left

Original holes: four. Closed in the item:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_sectionwise`.
This is a decomposition, not a net proof: one hole is closed and one is added.

The following three original holes are unchanged, all attached to
`lem-sf-ringed-restriction-exchange-open-descent`:

- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.openCube_exists`.
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_restriction`.
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.identity_normalization`.

Added hole:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.actual_open_square_alpha_normalization`,
node `lem-sf-ringed-open-square-unit-normalization`.
It is exactly the compositor/unit identification within the parent's step 6;
the rest of the sectionwise argument now consists of checked Lean proofs using
the existing sectionwise geometric comparison.

Actual holes after this delivery: three in the item and one in the new module;
four in total. No axiom or definition hole is added.

## No longer needed

None. No existing import, node, module or unit step is pruned. All existing public
imports are preserved. The added public import re-exports the unchanged coefficient construction.
The parent node keeps every existing dependency and adds the new normalization
node to step 6 and `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing open-restriction counit theorem supplies
an alpha characterized by its unit equation, whereas the selected ordinary
exchange uses `StrictTowerRingedSquare.exchangeModuleSquare`. These constructions
are not definitionally equal. The original step 6 requires an explicit
normalization identification between them. This delivery isolates that exact
identification and supplies the complete uniqueness and mate arguments that use
it. Empty schemes and zero coefficient rings require no additional assumption.

## New nodes

`lem-sf-ringed-open-square-unit-normalization`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-open-square-unit-normalization.json`,
states the unit normalization of the inverse selected actual-ring module square.
Its proof plan conjugates the three compositor factors, uses the existing
sectionwise normalization of each compositor, transports across equality of
coefficient-decorated scheme maps, and applies `unit_conjugateEquiv` on sections.
This is strictly a step of the original argument: it makes no assertion about
a sectionwise ordinary exchange. The public coefficient construction is relocated without changing its interface
or definition. The change record is
`coord/changes/ringed-open-square-shared-coefficients.md`.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
