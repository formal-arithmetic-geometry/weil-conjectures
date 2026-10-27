## What changed

Completed the open-adjoint argument using the normalized open-unit package and
existence of the specified coefficient action. Wrote the recorded compact-support
comparison by coherent finite-stage adjunction descent, adjoint uniqueness for the
open and proper factors, and the existing arbitrary-compactification compositor.
The finite rational proper-support adjunction is proved in a new module from the
strict identity-open tower comparison and the existing proved scalar-localization
construction. The separate coefficient-counit normalization is stated explicitly.
The open-unit auxiliary module has an independent coefficient-universe repair and
the canonical finite-inclusion pullback comparison. The optional rational compositor
naturality proof is retained in scratch; its original hole remains in the delivery.
No declaration of the adopted source library is changed.

## Proved and sorry left

Original item holes: `WeilConjectures.zlPull_open_isRightAdjoint` and
`WeilConjectures.zlCommonStageShriek_recorded` are filled. The latter is a
decomposition through a separate finite coefficient-counit compatibility result; this
compatibility remains an explicit gap. The new theorem
`WeilConjectures.properSupportFiniteAdjunction` is proved and has zero holes.

The retained original auxiliary hole is
`WeilConjectures.ZlOpenUnit.openWeilUnitAndEmptyFibre`
(node `lem-zl-open-weil-unit-and-empty-fibre`).
The new hole is `WeilConjectures.properSupportCoefficientAdjunction`
(node `lem-zl-proper-support-coefficient-adjunction`). It concerns only normalization
of finite proper adjunction counits against the prescribed coefficient maps.

The second retained original auxiliary hole is
`WeilConjectures.ZlOpenUnit.rationalAlpha_natural`
(node `lem-zl-open-weil-unit-and-empty-fibre`). A proof was checked in a diagnostic
version, but its import and proof are omitted from the packet to keep the auxiliary
file's elaboration cost within the limit.
In total: two original item holes closed and one strictly finite coefficient-normalization
hole added. The assigned item has zero remaining holes; the delivery has three holes,
including the two retained original auxiliary holes.
All remaining holes of imported modules stay in their defining modules and nodes.

## No longer needed

No module or DAG node is withdrawn. All original public imports and declarations
remain. The proof reuses the normalized open package, the strict identity-open
proper comparison, and the existing arbitrary-compactification field compositor.
No Frobenius-equivariant object theory or replacement coefficient category is added.

The old direct proof-dependency entries
`def-weil-compact-support-coefficient-action`,
`def-weil-integral-rational-qbar-compact-support`, and
`def-zl-weil-compact-support-cohomology` are replaced by the explicit normalized
open-unit, finite adjunction, coefficient compatibility, and composition results.
Their definitions remain available through the original public imports and statement
dependencies; this is no withdrawal or claim that those modules leave the closure.

## Where the brief, the DAG or earlier work was wrong

The parent allows independent scheme and coefficient universes; the open-unit
package's final section had specialized the coefficient closure to the scheme
universe despite its underlying action supporting independent universes. Its
point-cohomology predicate also used a restricted same-universe realization API.
The repair records vanishing at the literal finite point complex in every degree;
faithful extension of fields makes this equivalent to the old realization when
that realization is defined. The unchanged common-stage zero-object clause implies
both. The auxiliary package retained separated structure-morphism hypotheses through
its realization definitions. These are unnecessary for the open-unit argument:
finite type and quasi-compactness give Noetherian schemes, and Stacks 09BN/09BP
require no separated structure morphism. The auxiliary section is generalized.
The change record audits the three DAG citers and the zero current Lean consumers.
Local opacity annotations, explicit scalar-law parameters, and typed transport
helpers avoid repeatedly unfolding the realized functors. The witnesses and map
equations remain unchanged. All four packet modules compiled together in import order.

## New nodes

`lem-zl-proper-support-finite-adjunction` records the proved finite rational
proper-support adjunction, with no common-stage or Weil assertion.
`lem-zl-proper-support-coefficient-adjunction` records the separate finite
coefficient-counit normalization needed by the real stage-descent combination.
Change record: `coord/changes/C6-open-weil-independent-coefficient-universe.md`.

## Forced adaptations

### Sheaf.Paper.ZlOpenWeilUnitEmptyFibre
Original already fails against the compiled baseline (pre-existing):
```
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit
```
Adapted module compiled in the delivered set.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
