## What changed

Replaced the body of `WeilConjectures.ScalarExtensionTower.scalarTowerPullbackLimitSquare_mate`
by a proof from three strictly smaller normalization statements. Its signature, universes,
visibility and public imports are unchanged. The proof chooses a good representative using
localization essential surjectivity and applies the existing proved coherent quotient-presentation
existence theorem. It then cancels an explicitly defined invertible Roos-coordinate map, uses two
independent route calculations, and cancels the adjacent system isomorphism and its inverse.

Added `Sheaf.Paper.ScalarPullbackRoosCoordinates`, `Sheaf.Paper.ScalarPullbackLeftRoos` and
`Sheaf.Paper.ScalarPullbackRightRoos`. The first gives explicit definitions of the strict generator
normalization, target coordinate map and ordinary reference chain. None chooses data from an
unproved existence theorem. It also proves `scalarPullbackQuotient_computes`: transfer K-flatness
and termwise flatness through the finite evaluation isomorphisms, use the existing sequence-site
detection and inverse-image preservation results, and invoke derived scalar computability.
The coordinate isomorphism itself is chosen only locally in the theorem proof.

The remaining computations are separated by the realization data they use. The left statement
uses only the scalar model at Y and L-pullback model. The right uses only the scalar model at X
and E-pullback model. They identify their individual routes with an explicit localized ordinary
`scalarPullbackChain`, rather than asserting the original two-route equality again. Their common
coordinate-existence statement concerns only strict ordinary quotient tensors and pullback.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.ScalarExtensionTower.scalarTowerPullbackLimitSquare_mate`
(node `stage3-pur-scalar-pullback-limit-bridge`). Its complete combining proof depends on the three
new holes listed below, so this delivery is a decomposition, not a net proof of the obligation.

Proved without a new hole:
`WeilConjectures.ScalarExtensionTower.scalarPullbackQuotient_computes`, in the coordinate module.
All three coordinate definitions have actual bodies and no holes.

Added exactly three holes, each a whole named public theorem with its own source and proof in
words:

- `WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinates_exists`
  (`stage3-pur-scalar-pullback-roos-coordinates`): a strict quotient-tower isomorphism with the
  nested tensor-unit generator normalization; no completed realization equation.
- `WeilConjectures.ScalarExtensionTower.scalarPullbackLeftRoos`
  (`stage3-pur-scalar-pullback-left-roos`): compute the Y-scalar/L-pullback route in those coordinates.
- `WeilConjectures.ScalarExtensionTower.scalarPullbackRightRoos`
  (`stage3-pur-scalar-pullback-right-roos`): compute the E-pullback/X-scalar route in those coordinates.

Thus the delivered item itself has zero remaining holes; the new modules have three. One old
hole closed, three new holes added. Existing imported holes remain obligations of their owners.
Compilation checks every file separately in import order; the delivery command performs the
required preflight and dependent-module checks.

## No longer needed

Removed the private proof import `Sheaf.Paper.ScalarTowerPullbackStrictSquare` and the direct proof
dependency `stage3-pur-scalar-pullback-strict-square`. The original `_hstrict` hypothesis stays in
the signature but is unused: its strict tensor/pullback square is not needed for the new
scalar/pullback normalization calculation. The parent still uses that node, so this is removal
from this proof's dependencies, not a claim that the whole module is globally pruned.

The old direct `lem-pc-kflat-resolution` dependency is replaced in this item's assembly by the
proved good-localization and coherent-presentation APIs. K-flat resolution remains a proof
prerequisite of the new right-route normalization node and is not globally pruned.

No module is withdrawn, no declaration in the adopted source library is removed, and no unit
statement or realized proof step is bypassed. The item's unit record has no realized route entries.

## Where the brief, the DAG or earlier work was wrong

The strict-square hypothesis is `leftRoute = rightRoute` from
`ScalarExtensionTowerComparisonData`; those routes are the tensor/pullback compatibility square,
with two complex inputs. The assigned theorem concerns scalar extension versus pullback on one
input. The original prose treated the former square as if it directly computed the latter.
The theorem signature is preserved, but the proof now uses the actual scalar/pullback system
comparison and the ordinary `scalarPullbackChain`.

Postcomposing with the inverse system isomorphism alone leaves an equivalent obligation and
supplies no normalization calculation. The new proof additionally introduces a concrete strict
Roos coordinate, proves its derived scalar counit invertible, and separates the two independent
normalization calculations. Whole-system coherence is retained; equality is not inferred from
finite derived evaluations. The new statements were checked on the zero complex, quotient index
zero, identity morphisms, identity coefficients, empty sites, and ramified coefficient inclusions.
The tensor associators use no claim that a finite coefficient quotient is flat over the smaller
finite coefficient quotient.

The apparent existing completion/counit compatibility route cannot be imported here: those
modules depend on `ScalarExtensionTowerCoherence`, which already depends on this item.
No such cyclic import was introduced.

## New nodes

`stage3-pur-scalar-pullback-roos-coordinates` records the ordinary quotient-coordinate existence
statement and the separately proved pulled-quotient computability theorem, together with all
three explicit coordinate definitions. The remaining existence proof is ordinary balanced tensor
association followed by strict pullback and the tensor-unit generator formula.

`stage3-pur-scalar-pullback-left-roos` records the independent computation using SY and ML. It
normalizes scalar completion and L-pullback, compares quotient generators with the coordinate
formula and takes Roos before transporting along the good representative isomorphism.

`stage3-pur-scalar-pullback-right-roos` records the independent computation using SX and ME.
It compares a resolving representative of the pulled complex with the coherent pulled quotient
system, applies scalar normalization there, and uses the defining cochain equation of the system
comparison. Its conclusion is the explicit ordinary chain, with no realization at Y or L-pullback
realization appearing.

All three nodes inherit the item's chapter and unit and record the actual Mathlib searches.
Change record: `coord/changes/R3-scalar-pullback-roos-coordinates.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarPullbackLeftRoos": "6ae27fc14fdcd315db34e2b40fd18df92ec06d96", "Sheaf.Paper.ScalarPullbackRightRoos": "7b9eb3cb1a48f5d3e95b8b08dc33dabfcc53d05d", "Sheaf.Paper.ScalarPullbackRoosCoordinates": "0adb23e5a46d0e2b618a697955f54bebd2ae59b7", "Sheaf.Paper.ScalarTowerPullbackLimitBridge": "aa700c326d8cf77ed021154486d5837e117ea91d"}, "results": {"Sheaf.Paper.ScalarTowerPullbackLimitSquare": {"hash": "e7007e0e38d8a34171ecf7e21a72e31fe3c3eb3c", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T05:36:08+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
