## What changed

Proved `CategoryTheory.aut_fiber_transitive` in
`Sheaf.CategoryTheory.Galois.GaloisTransitive`, with its signature and visibility unchanged.
The proof bundles the finite fibers into `FintypeCat`, constructs Mathlib's
`PreGaloisCategory`, `FiberFunctor`, and `GaloisCategory` instances from the original
Stacks axioms, applies `FiberFunctor.isPretransitive_of_isConnected`, and forgets the
finite-type bundling by `isoWhiskerRight`. The summand axiom uses the existing proved
`stacksGalois_mono_complement`; exactness supplies finite-group quotients after a
universe reduction. This reproduces the comparison construction already used in
`AbstractEquivalence`, without importing that module or its theorem.

Added proof-only imports of `Sheaf.CategoryTheory.Galois.StacksMonoComplement` and
`Mathlib.CategoryTheory.Galois.Prorepresentability`. Updated `lem-galois-transitive`'s
proof, proof dependencies, and proof origin to match this route. No definitions,
public imports, other modules, or existing theorem signatures changed.

## Proved and sorry left

Closed the single original hole in `CategoryTheory.aut_fiber_transitive`
(node `lem-galois-transitive`): 1 of 1 proved, 0 split off, 0 holes added.
No `sorry` remains in the delivered Lean module.
Single-file compilation through `lcompile.py` succeeded in 2.0 seconds. The explicit
axiom check for `CategoryTheory.aut_fiber_transitive` returned exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the import `Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists`.
The declaration `CategoryTheory.exists_stacksGaloisObject_hom_of_isConnected` and
node `lem-galois-object-exists` are not needed by this proof. The standalone node
`lem-galois-inverse-limit-surjective` is also not a direct proof dependency: Mathlib's
proved transitivity theorem already contains the prorepresentability and finite
inverse-limit argument. `StacksGaloisAxioms` remains necessary both for epi detection
and for the imported summand theorem. `StacksGaloisCategory` remains the public
statement dependency. No other imports were removed. No global unreachability of
the pruned dependency modules is claimed; other library theorems can still need them.

## Where the brief, the DAG or earlier work was wrong

The earlier Mathlib search correctly required a comparison of the Stacks and SGA1
axioms before using Mathlib transitivity. That comparison is now available through
the proved `stacksGalois_mono_complement` and the instance construction already in
`AbstractEquivalence`; the four original Stacks-specific construction steps need
not be rebuilt here. No mathematical statement was repaired or weakened.

The assigned node is not in `sk-prop-h2`'s `realized.statement` or `realized.steps`.
The unit's Kummer argument and its dependencies are unchanged.

Searches: launcher `msearch.py` LeanFinder, Loogle with the full transitivity
instance name, and grep for `isPretransitive_of_isConnected`, plus local `rg` of
Mathlib Galois and the project Galois modules. Loogle and grep identify exactly
`CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected`;
the relevant signatures and the existing comparison proof were read in full.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
