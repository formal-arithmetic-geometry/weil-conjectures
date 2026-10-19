## What changed

Changed only proofs in `lean/Sheaf/SixFunctors/FrobeniusPointTransportNatural.lean`.
The rational pullback object formula follows directly from the specified uniqueness
property of `rationalDerivedPullback`. The common-stage formula combines its
specified object formula with that rational formula at the object's coefficient
stage. The qbar fibre object formula is the specified object formula of
`pointQbarFibre_existsUnique`. All existing statements, definitions, universes,
visibility, imports and docstrings are preserved.

The delivered module compiled successfully with `lcompile.py` (7.1 seconds before
the final notation-only replacement of a lambda arrow). This is a partial delivery
under the brief's rule for a module with several holes. The unfinished larger
naturality attempt and its diagnostic files remain in the sandbox scratchpad;
they are not part of the delivery.

## Proved and sorry left

Closed three of the four original holes:

- `WeilConjectures.frobeniusPointRationalPullbackEq`.
- `WeilConjectures.frobeniusPointQbarPullbackEq`.
- `WeilConjectures.frobeniusPointQbarFibreObjEq`.

One original hole remains, with its original full statement and `by sorry` proof:
`WeilConjectures.frobeniusPointTransport_natural`, node
`lem-weil-frobenius-point-transport-natural`.
No holes are added and no statements are split off. The delivered module has
exactly one `sorry`, all of it in that named public theorem. No definitions contain
`sorry`. The three completed proofs use the library's existing specified uniqueness
theorems, which are allowed stage-3 dependencies.

The retained attempt develops finite, integral and rational naturality. Its integral
comparison calculation was checked separately after replacing a rewrite by direct
transitivity and qualifying `CategoryTheory.Functor.map_id`. The full attempt is
not certified: the coefficient-extension and qbar clauses remain unfinished, and
none of its auxiliary helpers is claimed as delivered or proved here.

## No longer needed

None. No imports, nodes or modules are pruned. The remaining naturality theorem
still has its original proof plan and dependencies; these three preparatory object
identifications do not justify pruning that plan. Experimental added imports and
an experimental dependency-module copy are excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong

No statement defect is asserted. In the retained proof experiment, an unqualified
`Functor.map_id` selected the ordinary typeclass-functor theorem in a rewrite;
qualifying the categorical declaration fixed that calculation. Conversions between
the ring and commutative-ring presentations of the completed coefficient sheaf
also made rewrite-based proof attempts fragile. Neither observation changes any
published definition or theorem in this delivery.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
