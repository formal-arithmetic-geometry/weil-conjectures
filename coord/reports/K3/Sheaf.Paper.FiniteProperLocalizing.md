## What changed

Worked from the current rework source, preserving all definitions, public imports,
theorem statements, existing proofs, and the node's Lean attachment. Completed
`AlgebraicGeometry.ProEtale.finiteProperLocalizing_baseChange`.

The proof identifies the finite proper exchange on constructible finite-Tor generators
with the recorded ambient exchange. It uses the existing bounded etale-origin exchange
and coefficient-encoding comparison, followed by localizing minimality. Proper direct
image on both vertical legs preserves the required coproducts. Derived inverse images
preserve coproducts as left adjoints; constructible pullback keeps objects in the
localizing closure needed by the second direct image. A named explicit identity monoid
isomorphism retains the original continuous finite coefficient.
The equality between the two exchange presentations
and the bounded-generator calculation are proved in private generic lemmas, keeping
the concrete coefficient construction out of that calculation.

Added the fully proved module `Sheaf.Paper.CondensedAmbientExchangeTriangulated`.
Its theorem transports exact termwise shifts to inverse images and compatible shifts
to their right adjoints, then proves that the ambient exchange has a triangulated
isomorphism locus. The argument adapts the proved private helper in
`UnboundedBaseChangeExtension`, whose import here would create a cycle. Explicit shift
parameters on the mate theorem avoid expensive unresolved typeclass synthesis.
A private cached proof and a public wrapper keep the public statement independent
of local cache instances.
The helper is compiled separately after these optimizations.
The owned module also isolates the intersection calculation for arbitrary categorical
functors and uses canonical generator-inclusion and closure-elimination lemmas before
activating its tensor-instance caches. These preserve the recorded generating predicate.
The conversion from a scheme over the field to an `Over` object is performed while
the condensed coefficient is still a parameter, avoiding expensive kernel conversion
after specialization to the finite discrete ring.

The assigned module adds proof imports of that helper and the full body of
`FiniteProperExchange`. The helper uses proof imports for exact derived shifts,
adjunction shifts, triangulated adjunctions, and the existing cached instances.
Updated the owned DAG proof to match the argument.

Validation: `lcompile.py --all` accepted both final modules cleanly, with no errors
or warnings. The eight existing public declaration signatures and every public import
match the current live source. The packet contains zero `sorry` tokens.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteProperLocalizing_baseChange`
(node `det-ctf-finite-proper-localizing`).

Added no holes and split off no unproved statement. No `sorry` remains in either
delivered module. The existing proofs of `finiteProperLocalizing`,
`finiteOpenLocalizing`, and `finiteCompactificationLocalizing` are retained.
All dependencies are used with their existing statements; this report counts only
holes in the assigned module, without asserting that its entire dependency closure
is free of `sorry`.

## No longer needed

No mathematical dependency, module or import was pruned. The old private `extend_iso`
helper is refactored into `iso_intersection_localizing`, with the same coproduct
argument; recorded-generator minimality is handled separately.
The unit route and the quarantined module's Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The recovered preferred-upstream proof is historical: the current quarantine already
contains the adapted open-immersion proof and the proper-image proof. Its only remaining
hole was the localizing base-change theorem. The old claim that `finiteProperExchange`
was definitionally the ambient exchange needs an explicit equality: its equality
transport is identified using `finitePullbackCongr_eqToIso`.

## New nodes

`lem-sfb-condensed-ambient-exchange-triangulated`, in
`Sheaf.Paper.CondensedAmbientExchangeTriangulated`, states and fully proves the
triangulated isomorphism locus of the specified ambient exchange. It is valid for
any commutative condensed coefficient and any chosen Cartesian square. It is strictly
one part of the argument: coproduct closure, properness, and invertibility on generators
are established separately in the assigned module. Zero coefficients and empty schemes
satisfy the statement by the same categorical argument. No change record is required:
no existing interface or definition was changed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
