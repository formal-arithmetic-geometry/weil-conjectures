## What changed

Proved `AlgebraicGeometry.AffineSpace.affineLine_finiteGroup_devissage` in
`Sheaf.AlgebraicGeometry.AffineLineFiniteGroupDevissage`. Its signature, both existing
functor/adjunction constructions, and every public import are unchanged. Four private,
proved helpers establish the connected-scheme constants unit, cyclic-coefficient
vanishing, finite-coefficient acyclicity, and invertibility of the specified derived
constants map. The theorem docstring and its DAG proof now describe this argument.

The cyclic input is the existing Kummer root-line computation for every positive
invertible modulus. Mathlib's finite abelian-group decomposition and preservation of
finite biproducts by additive derived functors replace cardinality induction. The
acyclic-complex comparison proves that the actual canonical map is invertible;
naturality follows from its natural-transformation equation. Mathlib's p-group
cardinality theorem proves the order assertion.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.AffineSpace.affineLine_finiteGroup_devissage`
(node `lem-pur-affine-line-finite-group-devissage`). All five conjuncts are proved.
The item has zero remaining `sorry`s. Zero holes were added and zero statements were
split off. The four private helpers are completely proved. Existing imported
statements remain the project's independently assigned dependencies.

The proof includes the trivial group through the empty finite biproduct. Each cyclic
summand has modulus dividing the given exponent; no freeness over `ZMod (ell ^ a)`
is assumed. The specified theorem hypotheses, including `1 ≤ a`, are preserved.

## No longer needed

Removed these original proof-only imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`;
- `Mathlib.Algebra.Homology.ModelCategory.Injective`;
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`;
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`;
- `Mathlib.CategoryTheory.Sites.Sheafification`.

The direct proof no longer needs the following original proof-dependency nodes;
their obsolete top-level `tool_uses` entries are removed:

- `lem-weil-pbc-derived-functor-long-exact`: finite direct-sum decomposition avoids
  the short-exact-sequence induction;
- `lem-weil-pbc-sheafification-exact`: that induction's exact constant-sheaf sequence
  is unnecessary;
- `lem-weil-pbc-lift-along-injective-quasi-iso`;
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`;
- `lem-weil-pbc-bounded-below-homotopy-invariance`: the last three are unnecessary
  for coefficient naturality, already built into `abelianDerivedConstants`.

`def-weil-pbc-constant-sheaf` remains a statement dependency, rather than a duplicate
proof dependency. No module is withdrawn: dependencies may still be used elsewhere
or transitively by the existing derived-category infrastructure. The Kummer input
and the blueprint unit's geometric route are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was necessary. The DAG's cardinality induction
and explicit resolution-lift naturality argument were longer than needed with the
existing declarations: the Kummer input already treats composite invertible moduli,
and the specified constants comparison is already a natural transformation. The new
proof preserves the canonical comparison rather than choosing an arbitrary
isomorphism. No target statement, public definition, source-library declaration,
or unit statement/proof step was changed.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
