## What changed

Proved `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves_intrinsic`
without changing its statement. The proof uses the published actual-ring
direct-image/completion comparison, the existing ordinary pullback composition
and identity comparisons, and the derived adjunction for the inverse scheme
isomorphism. Two proved private helpers establish invariance under isomorphism
and preservation by derived direct image. The only input membership clause used
is `K.property.1`.

The completed comparison now obtains ordinary-pullback completeness directly
from this theorem, rather than from the conjunction of all three preservation
components. Its existing signature and construction remain unchanged.

Removed seven unused private proof helpers. Public declarations, definitions,
instances, and imports retain their signatures. Updated the intrinsic-preservation
node to record the actual proof. No other module is changed. The server compiler accepted the proof in 48.1 s;
the suggested `omit hf` removes its sole new unused-section-variable warning.
The delivery gate performs final compilation and axiom/preflight checks.

## Proved and sorry left

Closed one of the item's three holes:
`AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves_intrinsic`
(node `lem-wf-pbc-automorphism-transport-intrinsic`). Added zero holes and
split off zero statements.

Two original holes remain unchanged:

- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves_reductions`
  (`lem-wf-pbc-automorphism-transport-reductions`).
- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves_origins`
  (`lem-wf-pbc-automorphism-transport-origins`).

The completed comparison proof no longer depends on either remaining hole.
The new proof uses the already stated derived composition and identity
comparisons in `PbcActualRingedExchange`; their own proof obligations are
retained, not duplicated here.

## No longer needed

No public or private imports were removed. No DAG node or module is withdrawn.
The intrinsic-completeness argument avoids constructing a transported Koszul
witness or proving a separate inverse-image/derived-limit comparison: it uses
the existing direct-image/completion API and the inverse isomorphism instead.
The two other preservation components remain needed by integral transport.

Removed unused private declarations `isoTransportDerivedCounitComparison`,
`isoTransportDerivedCounitComparisonOfEq`,
`isoTransportModulePushforwardEquivalence`,
`isoTransportLocalization_naturality`, `isoTransportRationalComparison`,
`isoTransportFullSubcategoryEquivalence`, and `isoTransportCompletionUnit`.
A search of both source roots finds no consumer outside the original module.

## Where the brief, the DAG or earlier work was wrong

The intrinsic-preservation plan suggested rebuilding and transporting the
completion witness. The already available actual-ring completion comparison
makes that unnecessary. Stacks `proetale.tex`,
`lemma-pushforward-Noetherian-case` (Tag 099N), clauses (1) and (3), supplies
the relevant direct-image preservation argument. Pullback along an isomorphism
is identified with direct image along its inverse using the existing derived
adjunction, compositor, and identity comparison. This works for the original
general adic datum, including empty schemes and the zero object; it adds no
Noetherian-scheme, dimension, or coefficient-field hypothesis.

The existing constructible-reduction pullback theorem is restricted to
Noetherian schemes and valuation-ring data, so it does not prove the two
remaining components at their stated generality.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
