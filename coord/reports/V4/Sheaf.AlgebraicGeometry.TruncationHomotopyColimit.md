## What changed

Proved `AlgebraicGeometry.Etale.isIso_truncationHomotopyColimit_comparison` in
`Sheaf.AlgebraicGeometry.TruncationHomotopyColimit`, preserving its exact statement
and the current shared repository's public imports. Updated the theorem's proof explanation and its
existing DAG node to match the proof.

The comparison comes from exactness of Hom on the specified telescope triangle.
Three completely proved private helpers compute the cokernel of an eventually
invertible sequential cocone, compare derived telescopes on homology, and prove
that upper truncation inclusions induce homology isomorphisms below the cutoff.
The proof uses the existing sequential telescope monicity theorem, source-library
preservation of coproducts by derived homology, and Mathlib's homology sequence and
isomorphism detection. No object is chosen from an unproved existence theorem.

The complete file compiles cleanly through `lcompile.py`. An explicit
`#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
the diagnostic command was removed afterward. No source-library or consumer files
were changed. The unit record has no realized statement or proof steps, so this
shorter route changes no required unit route.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isIso_truncationHomotopyColimit_comparison`
(node `lem-kun-hocolim-truncations`).

Added 0 holes; split off 0 statements. There are 0 `sorry` occurrences in the
item module. All three private helpers are fully proved. The axiom audit also
checks the dependencies actually used by the final theorem.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`;
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (its supporting vocabulary is
  already supplied by the retained direct public imports of coefficients, sheaf
  cohomology, the derived t-structure, and the homology sequence).

The node `lem-kun-complex-colimit-hocolim` and its module
`Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit` are unnecessary for this
proof: computing the telescope after homology avoids choosing a complex
representative and transporting between two telescope triangles. Its descendants
need not be proved for this edge. The definition nodes
`def-weil-pbc-derived-categories`, `def-kun-truncations`, and
`def-sbc-standard-tstructure-derived-category` remain in use. The proof instead
uses the proved node `lem-kun-sequential-telescope-mono`. No global claim is made
that other consumers no longer need the removed dependency.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was necessary. The planned complex-level
argument can be shortened using the already proved source-library result that
derived homology preserves coproducts. Eventual invertibility in each homology
degree suffices; no normalized comparison between cochain and derived truncations
is needed. The proof handles negative degrees using `r.toNat`, the boundary
`r=n`, the zero object, and arbitrary unbounded complexes. The local exactness
instances are supplied at explicit universe sizes to avoid ambiguous instance
search. No launcher or timeout was changed.

The first dry run detected the obsolete wrapper import
`Sheaf.AlgebraicGeometry.DerivedCategories`, removed concurrently from the shared
repository. The sandbox now follows the current shared item, which already imports
its supporting upstream definitions directly. No replacement module was created.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
