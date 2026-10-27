## What changed

Proved `WeilConjectures.CompactSupportPbcProjection.forward` by applying
`CompactSupportWeilProjection.restriction` to the inverse coefficient presentations,
then mapping its isomorphism through the finite fixed-pair comparison and the
identity-carrier exact/completed bridge. The `finite_functors` normalization fixes
the underlying coefficient arrow. Faithfulness of the two forgetful maps proves
uniqueness. Proved private carrier and transport lemmas carry out the argument over an
abstract coefficient field and functor before specialization. An explicit
proof-irrelevance rewrite aligns the finite-dimensionality proofs in the two
coefficient presentations, avoiding expensive unfolding of their category models.
No public statement, definition, import or exported reducibility changes.
The item's node records this transport step and retains the other proof plans.

Validation: the cleaned module compiles without warnings through `lcompile.py`
in 25.4 seconds. Original public signatures, definitions and imports are unchanged;
the only existing theorem body replaced is `forward`.

Searches: launcher leanfinder for fixed-pair isomorphism transport, loogle for
`CategoryTheory.Functor.mapIso`, launcher grep for `IsoAlgebra.mapOfNatIso`, and
local searches in both library roots. The existing fixed-pair restriction and
`FdFrobeniusComparison.finite_functors` supply the exact route, with Mathlib's
`Functor.mapIso` and `Iso.ext`; no new statement is needed.

## Proved and sorry left

Closed 1 of the 5 original holes:
`WeilConjectures.CompactSupportPbcProjection.forward`
(node `fix-prop-projection-formula`, also attached by `sk-rem-sf-pf-done`).
Added 0 holes; split off 0 statements. This is a partial delivery of the module,
using its already stated framework restriction theorem as intended by stage 3.

The four untouched holes, all attached to `fix-prop-projection-formula`, are:

- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`.
- `WeilConjectures.CompactSupportWeilProjection.restriction`.
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification`.

## No longer needed

None. No import or dependency is removed. The remaining obligations retain the
existing finite/integral/field, open/proper mate, coefficient comparison and
Weil tensor routes. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The source already marks `CompactSupportPbcTransport.bridge_existsUnique` as
`STATEMENT-DISPUTED`: its normalization compares the reflector-completed source
with the strict-tower source by `HEq`, omitting the inverse of the canonical
`pbcActualCompletedPullback_tower` comparison. That comparison is an isomorphism,
not an equality of source objects. This delivery preserves that warning and
statement and does not claim to repair or prove it. The new proof uses the
existing bridge only for transport of fixed-pair structures; its underlying
functor is the identity, so the arrow calculation does not unfold the bridge.

The node's attachment of `lem-fix-weil-operations` currently names
`AlgebraicGeometry.Etale.isWeilPairing_mixedSupportCupProduct` in the source
library. That finite-etale pairing theorem does not directly supply the rational
proper/open projection's equivariance required for `restriction`. No replacement
of this unfinished obligation or false reduction was introduced here.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
