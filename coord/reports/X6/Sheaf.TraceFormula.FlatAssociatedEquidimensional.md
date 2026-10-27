## What changed

Proved `AlgebraicGeometry.flat_associated_equidimensional` in
`Sheaf.TraceFormula.FlatAssociatedEquidimensional`, preserving every existing
signature, definition, and public import. Added only proved private helpers for
closure inclusions, the equivalence of the two relative-assassin presentations,
the homeomorphism between the two fibre presentations, and finiteness of the
irreducible generic-fibre dimension. The main proof applies the already stated
`AlgebraicGeometry.flat_relative_associated_specialization` and uses scheme
sobriety to choose a generic point of each component.

Validation: the assigned module compiled cleanly through `lcompile.py` in 9.2 seconds.
Every original declaration signature was compared verbatim; all are preserved.
The DAG proof-dependency union matches its steps and all Lean lines are at most
100 characters. The delivery tool performs the final declaration/axiom checks.

The node proof now describes the actual topological fibre comparison and the
proved affine-open finite-dimension bound. Its dependencies are retained.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.flat_associated_equidimensional`
(node `lem-trf-flat-associated-equidimensional`). No holes remain in the item;
no holes or new public statements were added or split off.

The proof uses the existing pointwise specialization theorem, which still has
its own `sorry` in `Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization`.
This delivery proves the requested statement from that declared dependency;
it does not claim that the resulting transitive axiom closure is sorry-free.

## No longer needed

No imports, dependency nodes, or modules are pruned: all three existing proof
imports are used, and each planned dependency remains relevant to the proof.
The scheme-theoretic residue-field comparison suggested by step 1 is unnecessary:
`Scheme.Hom.fiberHomeo` identifies both fibres with the same topological subspace,
using the injective closure inclusion and its factorization identity.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The item and pointwise input use
independently defined relative-assassin presentations, one existential and the
other using `asFiber`; their equivalence is proved privately using the embedding
of `fiberι`. The explicit `Module.compHom` flatness and the pointwise theorem's
restriction-of-scalars flatness agree definitionally after transporting the
ambient point.

The finite-dimension node records a quasi-compact upper bound, whereas this
proof uses the more directly applicable, already proved affine-open non-infinity
bound from the same recorded module. The whole generic fibre is not assumed
quasi-compact. Nonemptiness rules out bottom separately. Empty special fibres
are handled vacuously, and no global Noetherianity of the base is assumed.

Source read: Stacks Project More on Morphisms Tags 0GSJ and 0GSI, including the
component-dimension equality in the second paragraph of the 0GSI proof. The
unit `sk-i-curve-zero` and its route are unchanged. Searches used the prescribed
LeanFinder, Loogle and grep services and local source searches; no shorter
existing theorem for the full result was found.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
