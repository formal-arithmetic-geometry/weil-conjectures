## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.connected_cover_open_subgroups` in
`Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups` without changing its signature.
All four clauses have complete Lean proofs. Proved private helpers establish
fibre cardinality equals degree, reflection of connectedness from transitivity, and
the pointed isomorphism criterion, open stabilizers, and realization. The open-subgroup realization transports the finite
coset action to a finite ordinal in the correct universe before applying essential
surjectivity. No definitions, public imports, other modules or target statements changed.

The proof uses the existing finite-etale Galois-category instances with Mathlib's
full action functor, essentially surjective continuous-action functor, transitivity,
open stabilizers and orbit-stabilizer theorem. It avoids the stronger FLC comparison
and base-change package. Updated the node's proof and proof dependencies to this route.

Validation: the complete module compiled through lcompile.py, and compiled again after
removing the three unused proof imports (6.8 seconds, no diagnostics). The delivery tool
checks compilation and all declaration axioms independently.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.FiniteEtale.connected_cover_open_subgroups`
(blueprint `cor-galois-open-subgroups`).

Added 0 holes; split off 0 obligations; no `sorry` remains in the delivery.
All private helpers are proved. This is a proof, not a decomposition.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`: the proved finite-etale
  Galois-category interface and Mathlib equivalence suffice; neither the FLC comparison
  nor the fundamental-group base-change clauses are needed. Accordingly the proof no
  longer depends on `thm-galois-fundamental`.
- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`: connectedness follows by
  the elementary monomorphism/fibre criterion and the already proved
  `connectedSpace_of_isConnected`. The proof does not use
  `lem-galois-coproduct-copies-morphisms-clopen`.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`: already supplied by
  the retained Basic and Connected imports; no additional direct import is needed.

Also removed `lem-galois-geometric-fibre` from the proof dependencies: the existing,
proved algebra-map equivalence and etale-algebra cardinality theorem give the required
fibre degree directly, without a chosen scheme coproduct splitting. The original public
imports are preserved to retain the exported statement interface. No module is withdrawn:
other parents may still use each removed dependency.

## Where the brief, the DAG or earlier work was wrong

The DAG's converse-connectedness step needlessly constructs maps into two copies of the
base: the source library already proves `connectedSpace_of_isConnected` and its converse.
Likewise the stronger FiberEquivalence theorem is unnecessary: Mathlib's abstract
Galois-category interfaces apply directly to the proved finite-etale instances.

The current main-20261015 blueprint repeats the previously corrected classification
error: unpointed covers classify conjugacy classes, whereas pointed covers classify
individual open subgroups. It also reverses subgroup containment for maps G/H→G/H'.
This delivery retains the assigned, already corrected statement and proves its pointed
and conjugacy formulations exactly; it makes no statement change.

The node for `def-galois-fibre-functor` now records the FLC stalk interface, while this
unchanged theorem uses the existing finite-etale geometric fibre. The proof uses the
canonical evaluation action and topology already provided for that finite-etale functor;
it does not replace either fibre convention.

No new nodes or unfinished intermediate statements were needed. The private helpers
are local parts of the complete argument, all proved from the existing library.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
