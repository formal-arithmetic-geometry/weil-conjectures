## What changed

Proved `AlgebraicGeometry.Etale.finiteEtaleOpen_uniformTorImage` in
`Sheaf.SixFunctors.FiniteEtaleOpenUniformTorImage`, preserving its complete signature
and every public import. The proof follows the six existing DAG steps:

1. Finite relative torsion dimension and `csInf_mem` produce its natural-number
   value and its defining torsion-abelian vanishing bound.
2. Over a finite ring, every section module is additively torsion. The existing
   higher-image coefficient comparison, faithful forgetting, and bounded-below /
   unbounded derived compatibility give the required all-module bound.
3. Finite modules over the finite Noetherian coefficient ring are finitely presented.
   Apply the existing finite-constant projection theorem and cancel the invertible
   canonical constant-pullback identifications to recover the original projection
   component, without changing its map.
4. Bounded constructibility supplies a bounded-below representative and an upper
   bound. Apply the existing finite-constant Tor-test theorem with the relative d.
5. The existing stalk / filtered-union theorem extends the tests to every sheaf.
6. The given prime power annihilates A and is invertible in k, hence on Spec k.
   The existing finite-coefficient open-image theorem supplies constructibility.

Added private proof imports for derived Plus compatibility and finite Noetherianity.
Updated steps 2 and 3 and the proof origin of
`lem-sfb-finite-etale-open-uniform-tor-image` to describe the actual Lean glue.
The set of mathematical proof dependencies is unchanged. No definitions, instances,
targets, public signatures, or other modules were changed.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Etale.finiteEtaleOpen_uniformTorImage`
(node `lem-sfb-finite-etale-open-uniform-tor-image`).

Added 0 holes; split off 0 statements. The delivered module contains no `sorry`.
Remote single-file compilation passed without errors or warnings in 43.7 seconds.
A text comparison confirms the theorem signature and public imports are unchanged;
all Lean lines are at most 100 characters. No scratch Lean files were created.
Imported declarations retain their existing proof status; this is a proof from the
existing library, not a claim that their full transitive axiom closure is already closed.

The proof keeps the coefficient-independent equality d = cd(j), every integer
cohomological degree, the original canonical projection components, and testing
against all module sheaves. It does not assume an algebraically or separably closed
field. Finiteness / torsion / Noetherianity and every invoked theorem permit the zero
ring and empty schemes. No positive dimension or nonzero coefficient hypothesis is added.

## No longer needed

Removed the private import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
this proof uses ordinary etale categories throughout. No declared DAG dependency is
pruned; all seven original proof dependencies are used. No module is withdrawn.

Searches before proving: Lean Finder for the full relative Tor-bound statement found
only scheme etaleness lemmas; Loogle for finite Noetherian rings did not provide the
combined theorem; the msearch grep for the dimension and item declaration had no hits.
Repository searches found the separate dimension, comparison, projection, finite-test,
stalk-extension, constructibility, and Plus-compatibility results used here.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The projection theorem exposes
its component only after composing with constant-pullback isomorphisms; its direct
component helper is private. Cancelling those isomorphisms provides the required
publicly usable consequence without an interface change or additional statement.
Finite coefficients already make every module additively torsion, so step 2 does not
need to transport the given prime-power annihilation through each section functor.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
