## What changed

Proved `AlgebraicGeometry.etale_local_ring_flatness` in
`Sheaf.TraceFormula.EtaleLocalRingFlatness`, with its signature and public imports
unchanged. The proof gives the stalk map its canonical algebra structure and
uses Mathlib's `LocallyOfFiniteType.stalkMap` and
`FormallyUnramified.stalkMap` to apply
`Algebra.FormallyUnramified.flat_of_restrictScalars` for the forward implication.
`Flat.stalkMap` and `Module.Flat.trans` give the converse. The ring-module
construction `Module.addCommMonoidToAddCommGroup` supplies additive inverses
without adding a hypothesis or changing the existing additive monoid.

Replaced the three old private project imports by the private proof import
`Mathlib.RingTheory.Unramified.Finite`. Updated the node's proof,
proof dependencies and proof origin to the implemented algebraic argument, and
removed the obsolete relative-flat-extension tool approval. No definitions,
public interfaces, consumers or unit-level routes change.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.etale_local_ring_flatness`
(node `lem-trf-etale-local-ring-flatness`). Zero holes added, zero split off,
and zero holes remain in the delivered module. This is a proof, not a
decomposition. The module compiles through `lcompile.py`; delivery preflight
also checks the declaration's axioms.

The proof keeps the independent universes `u` and `v` and handles all modules,
including the zero module. Empty source schemes provide no point `t`. For the
identity morphism the equivalence reduces to flatness over the same ring.

## No longer needed

Removed private imports:

- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` (the statement needs only
  Mathlib's scheme stalks, not the sheaf-module stalk functor).
- `WeilConjectures.AlgebraicGeometry.PullbackStalkRelativeFlatExtension` (the
  direct formally unramified algebra lemma replaces base change and the
  diagonal tensor identification).
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism` (Mathlib's
  `FormallyUnramified.stalkMap` supplies exactly the algebra property needed).

Removed proof dependencies `def-pc-fibre-product`,
`def-weil-unramified-morphism`, `def-weil-open-immersion`,
`def-weil-locally-ringed-space-morphism`,
`lem-pc-pullback-stalk-relative-flat-extension`, and
`def-weil-pbc-flat-ring-map`: none supplies a proof step on the new route.
`def-weil-pbc-flat-ring-map` remains a statement dependency as the definition of
flatness. `def-pc-module-stalk-functor` likewise stays in the unchanged statement
dependencies. No module is withdrawn or claimed globally unused; other
consumers may still need all these declarations.

Added the existing Mathlib leaf `lem-sc-unramified-flat-of-base-flat` as the
forward proof dependency. Its existing source and Lean attachment were read;
no new node is necessary.

## Where the brief, the DAG or earlier work was wrong

The planned open-diagonal proof is valid, but unnecessary here. The node's
Mathlib candidate was previously rejected because the comparison of the
scheme stalk map with an essentially finite type formally unramified algebra
was not yet made. Both comparisons are already in Mathlib, so the algebraic
candidate supplies a short complete proof. It also avoids the universe
restriction of `pullback_stalk_relative_flat_extension` to `ModuleCat.{u}`.

Searches: `msearch.py` LeanFinder for the etale stalk and restricted-flatness
statement; `msearch.py` Loogle for
`Algebra.FormallyUnramified.flat_of_restrictScalars`; and `rg` over Mathlib,
`lean/WeilConjectures`, `lean/Sheaf`, and the DAG. Read the exact theorem and
its variables in `Mathlib/RingTheory/Unramified/Finite.lean`, the stalk-map
lemmas in the scheme morphism files, and Stacks `flat.tex` labels
`lemma-etale-flat-up-down` and `lemma-etale-flat-up-down-local-ring`.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
