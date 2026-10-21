## What changed

Reused the proved adopted `AlgebraicGeometry.mixedInternalHom_baseChange_exchange`
in `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange`. Replaced the private import
of `Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange` with
`WeilConjectures.AlgebraicGeometry.MixedInternalHomBaseChangeExchange`.

The new proved private `schemeHomTensorPullbackIso_eq_mixed` identifies the
compatibility tensorator with the adopted tensorator by extensionality and reflexivity.
Rewrite by this equality and unfold `mixedHomDirectImageComparison`; proof irrelevance
identifies the chosen direct-image comparison, whose existential proposition is the
same. The existing local internal exchange equation now follows from the adopted
source proof. The global-sections mate and generic adjunction naturality argument
remain unchanged. The public theorem signature is byte-identical to the active
original, and its public import is unchanged. The node now records this actual route.

Validation: the revised module compiled without warnings in 35.4 seconds.
Import-direction checking confirms no cycle. Line lengths are at most 100 characters.
The artifact-producing compile passed for the revised module (43.6 seconds) and
the exact-signature public consumer (4.8 seconds), without warnings. The scratch
consumer is outside the delivery.
Change record: coord/changes/G3-global-hom-exchange-adopted-internal-proof.md.

## Proved and sorry left

`AlgebraicGeometry.schemeGlobalHom_baseChange_exchange` remains completely proved
from its imported declarations. The assigned rework module has zero textual holes:
0 of 0 holes closed, 0 holes added, 0 split off, 0 left in the item. The new private
`schemeHomTensorPullbackIso_eq_mixed` is fully proved with no sorry.

The existing imported `AlgebraicGeometry.schemeGlobalSections_baseChange_mate`
(node lem-sc-global-sections-base-change-mate) retains its original sorry. It is not
created or changed here. No claim is made that the whole dependency closure is free
of sorry. The unfinished `AlgebraicGeometry.schemeInternalHom_baseChange_exchange`
is no longer used or imported by this proof.

## No longer needed

Removed the private import `Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange`
and the proof dependency `lem-sc-internal-hom-base-change-exchange`. The proof now
uses the adopted proved mixed internal exchange, after identifying its canonical
data, instead of requiring the unfinished duplicate internal-exchange theorem.
The old module has no other active Lean importers; the quarantine archive still
records the historical import. It is left intact, not deleted or withdrawn.

No other imports or dependencies are removed. The unit statement and its steps are
preserved: this changes only which existing internal-exchange theorem realizes the
same internal step below the unit level. No adopted declaration is deleted or
replaced with a sorry.

## Where the brief, the DAG or earlier work was wrong

The rework assignment names a historical global-build failure already repaired by
M2 in commit 7d9ef47ab3f (landing 20261021T214830-L-1864636). The current source compiles
before this delivery. Repeating that repair or changing its formatting would be a
no-op. This delivery instead makes concrete pruning progress using the now-adopted
proved internal exchange.

The earlier M2 report said the mixed exchange constructions differed. The remaining
difference in the tensorator is only reconstruction of an isomorphism from its
chosen hom, eliminated by extensionality and rfl; the direct-image choices select
from the same existential proposition and agree by proof irrelevance. No mathematical
statement, definition, target signature, or source-library boundary changes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
