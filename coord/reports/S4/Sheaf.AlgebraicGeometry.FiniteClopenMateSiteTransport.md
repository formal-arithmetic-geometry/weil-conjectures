## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.finiteClopenMateSiteTransport` with a
proof of the properness clauses, etale normalization, proper-mate transport and all
four invertibility assertions, using the separate alpha comparison theorem.

The private lemma `transport_mate` proves the categorical calculation: transpose under
the second proper adjunction, precompose with the pullback comparison, use naturality
of alpha and the first counit equation on one route, and naturality of the second
counit and its comparison equation on the other route. `mateEquiv_counit` identifies
both resulting expressions. This proof is independent of the geometric alpha result.

Moved the six canonical construction definitions unchanged to
`Sheaf.AlgebraicGeometry.FiniteClopenMateData`, publicly reexported by the item. This
permits the new alpha theorem to mention those actual constructions without an import
cycle. The original public imports remain available and no consumer signature changes.
The change record is `coord/changes/finite-clopen-mate-data.md`.

Validation so far: all three delivery modules compile through `lcompile.py`, with
no errors or warnings. A byte comparison verifies that the original theorem signature
and the six relocated construction bodies are unchanged. All import-direction checks
passed. The unchanged direct consumer, `Sheaf.Paper.SystemCompatibleCompositorNormalization`,
also compiles against the sandbox outputs (6.9 seconds).

## Proved and sorry left

Original holes: 1, at `AlgebraicGeometry.ProEtale.finiteClopenMateSiteTransport`.
That declaration now has a complete proof from named dependencies, including the new
alpha theorem. The private `transport_mate` is fully proved. There are no holes in
the item or in any definition.

Added holes: 1, at `AlgebraicGeometry.ProEtale.finiteClopenAlphaSiteTransport`, node
`lem-cbc-finite-clopen-alpha-site-transport`. This is precisely the geometric alpha
compatibility and its exact localization, before taking proper mates. It contains
none of the proper-mate equation, etale normalization or invertibility conclusions.
This delivery is a decomposition (1 hole closed and 1 strictly smaller hole added),
not a net reduction in the hole ledger.

The six relocated definitions add zero holes. The existing dependencies
`etaleClopenMateNormalization` and `etaleClopenMateResolution` are unchanged; the proof
uses only the former's bounded-below normalization clause.

## No longer needed

Removed the item's private proof imports
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange` and
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`. The corresponding
base-change nodes remain needed by the new alpha theorem; they are not globally pruned.

The parent proof no longer directly uses the geometric beta and projector argument,
or proper/open interchange coherence: alpha transport and etale normalization now
provide these separate results. Their nodes remain below those lemmas. No module is
withdrawn and no globally needed dependency is claimed as pruned. All original public
imports are retained for consumers.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or signature repair. The original seven-step plan combines a
geometric/exact-localization comparison with a categorical mate calculation. They are
separated here, with the latter proved in Lean. The original constructions and their
normalizations are preserved, including empty opens, empty complements, identity
squares and the zero ring. These edge cases do not change the unit, counit, or
disjoint-open gluing arguments of the remaining alpha theorem.

The resumed sandbox reference clock was reset by the dispatcher: the previous session
recorded start `1792758283.0783918`, whereas the current `.budget` records
`1792769017.7449467`. The interrupted compile attempt was session 45602; resumed
attempts include 70880, 21163 and 3681. No budget metadata was edited by this worker.
The first retained result reported the launcher's compile-service repair notice; all
following source checks have used the required `lcompile.py` unchanged. Delivery
attempt 44385 was refused by the split-off proof policy at 58 minutes, with no push;
work continued on exact-localization factorization and restriction detection.

## New nodes

`def-cbc-proetale-clopen-mate-data` records the six existing, now relocated canonical
constructions. No object is chosen from a mere existence statement and no definition
contains a hole. The existing item's Lean attachment now lists only its theorem;
the data node lists the relocated declarations.

`lem-cbc-finite-clopen-alpha-site-transport` isolates original proof steps 2--4. Its
statement is the alpha comparison on bounded-below objects only. Its docstring and
node give the cartesian open-unit comparison, identity/zero clopen projector comparison,
compositor calculation and exact-localization argument. The localization step now names
the already proved `rightDerivedFunctorPlusBaseChange_cube` and specifies every edge
and face in its application. The parent proves all the
proper-mate and invertibility consequences from this statement using actual Lean
composition, naturality, adjunction injectivity and cancellation.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
