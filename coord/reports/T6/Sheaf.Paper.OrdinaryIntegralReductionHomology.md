## What changed

Proved `WeilConjectures.ordinaryIntegralReductionHomology` in its existing module.
The statement, docstring and original public imports are preserved. All added
helpers are private and proved; no other existing module is changed.

Choose a flat-term K-flat resolution of a cochain representative of K. The actual
ordinary pullback counit computes ordinary pullback on this representative. The
ringed-topos K-flat preservation theorem lets the actual scalar-reduction counit
compute finite reduction of its pullback. The finite comparison already used in
the normalized pullback tower identifies the ordinary module constructions.
Uniqueness of left adjoints identifies its finite pullback with the prescribed
constant-coefficient pullback. Map this square to cochain complexes, localize,
apply homology and use the existing exact constant-coefficient homology comparison.
Transport along the localized resolution to obtain the stated isomorphism for K.

The complete proof compiled without errors or warnings in 11.5 seconds. The
delivery tool performs the final compile with the axiom and hole probe.

The proof imports expose existing private comparison helpers for use only in this
proof. The node copy records this argument and its K-flat preservation dependency.
No new declarations with postponed proofs, definitions, modules or DAG nodes are added.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.ordinaryIntegralReductionHomology`
(`lem-fix-ordinary-integral-reduction-homology`).

The item has zero remaining sorries. Zero holes are added or split off. This closes
one hole using existing dependency declarations; it does not assert that every
transitive dependency of those declarations is already sorry-free.

## No longer needed

None. All original public imports and all originally planned direct dependencies
remain needed. No module or node is withdrawn, and no unit route is bypassed.
The proof uses the finite comparison inside the normalized tower construction;
it does not need a new derived-comparison theorem or an additional descent lemma.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The missing passage from the underived tower
comparison to the specified derived objects is completed using the existing
computation counits on one flat-term K-flat representative. No new abstraction of
that same obligation is necessary. The K-flat preservation step is made explicit
in the updated proof dependencies. The unit record has no realized statement or
steps to bypass. The argument applies unchanged to the empty scheme, zero input,
and n = 0 (the first positive quotient exponent).

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
