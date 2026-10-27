## What changed

Completed the proof of `WeilConjectures.IntegralObjectQuotient.finiteNormalizedBasis`.
The proof builds the scalar-extension basis, identifies the object pullback by
uniqueness of left adjoints, transports the slice generator, and then compares the
single complexes. The inverse formula follows from linearity and the transported
value at `1`.

The module imports the two proof-only APIs used by this route:
`Sheaf.Paper.ScalarExtensionDualLocalIso` and
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`.
The local carrier declaration `finitePullback` is `noncomputable def` rather
than `abbrev`, with the same term and signature, and is marked irreducible locally
for theorem elaboration. The change is recorded in
`coord/changes/integral-object-finite-basis.md`.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralObjectQuotient.finiteNormalizedBasis`.
No `sorry` remains in the item module and no new statement was split off.

## No longer needed

No imported module or DAG dependency was withdrawn. The proof uses the recorded
scalar-extension dual local isomorphism, integral-operations comparison, pro-etale
inverse-image/restriction comparison, and weakly-etale localization route.

## Where the brief, the DAG or earlier work was wrong

The retained proof was blocked before elaboration because the published build was
missing upstream object files. After seeding those existing source objects, the
proof exposed and repaired the final single-complex cancellation. The original `finitePullback` abbreviation caused repeated unfolding of a large
homological-complex expression. Making it a semireducible definition preserves
its meaning and, with the local irreducibility attribute, keeps elaboration
bounded.

## New nodes

None.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
