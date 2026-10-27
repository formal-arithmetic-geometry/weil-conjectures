## What changed

Proved `CategoryTheory.ringed_equivalence_slices` using private constructions of the
slice equivalence, its geometric ring data, and the comparison of module inverse
images. The construction uses the supplied fibre equivalences and the existing
`SheafOfModules.ringData_inducedModules`; the module comparison works for every
presentation package quantified in the statement. Updated the node's proof route
and proof dependencies to describe these constructions. Module restriction is
implemented privately by precomposition, with an explicit natural isomorphism to
the public restriction functor; this avoids repeated scalar-restriction unfolding.
All private helpers are proved; no auxiliary modules are added.

## Proved and sorry left

Closed the one original hole in `CategoryTheory.ringed_equivalence_slices`
(`lem-weil-pbc-ringed-equivalence-slices`). No new holes or split statements.
Actual remaining hole count in the delivered module: zero.
The complete module compiled without warnings through `lcompile.py` in 34.3 seconds.
The original theorem signature is byte-for-byte unchanged.

## No longer needed

The proof does not use `lem-weil-pbc-ringed-topoi-module-adjunction`
(`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`). The existing induced
module construction supplies precisely the direct-image data needed here; the
module inverse-image comparisons follow from the specified adjunctions and their
linearity field. This removes that node from this proof's direct dependencies,
without withdrawing its module or any declaration. No original import was removed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition correction was needed. The DAG's geometric and module
comparison argument is realized explicitly; the induced-module construction is a
more direct interface for its second step than the previously listed general
module-adjunction theorem.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
