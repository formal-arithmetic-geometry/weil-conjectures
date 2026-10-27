## What changed

Proved `Algebra.PolynomialHomology.computationData_exists` in
`Sheaf.RingTheory.PolynomialPresentationHomology`, preserving the theorem signature and existing docstrings. Added proved private lemmas
and an explicit normalized comparison-family construction. Its proved existence
statement fixes every component to the supplied `Computation.comparison`; its
normalization determines the family, and no unproved existence is used.

Repaired the implementation of `ComputationData`: its six field types and their
dependencies are unchanged, but it specializes `ComputationPackage`, whose fields
are abstract. This avoids repeatedly checking the large presentation and derived
category expressions in generated record auxiliaries. The original concrete record
alone took 29.2 seconds; the generic record with the polynomial-resolution helpers
took 13.2 seconds. The change record is
`coord/changes/polynomial-computation-record.md`. The returned landing identified the consumer
`Sheaf.RingTheory.PolynomialSquareBarNaturality`; it now directly imports Mathlib and expands the old
reducible alias verbatim at its three use sites. The existing imports supply all APIs used by the proof.

The proof follows Stacks 08PS: polynomial evaluation gives the bijection between
augmentation-preserving maps and generator images, with no finiteness or surjectivity
hypothesis. Pointwise pullback coordinates give the required simplicial isomorphism.
Boundary lifting survives universe lifting, base change and arbitrary products.
The existing `SSet.exists_section_homotopy_equivalence` gives representable
contractibility. The supplied `Computation bar` gives the normalized comparison;
its evaluation and bar generator formulas identify identity-ring coefficient maps,
and its naturality and identity equations prove both required naturality assertions.
No data is selected from an unproved existence theorem.

Also repaired `colimitDerived` to specialize `colimitDiagram`, an explicit functor
with `obj F := derivedColimit bar F` and exactly the original composite map. This
avoids repeated conversion checks in comparison-family normalization. The functor
is definitionally equal to the original composite. See
`coord/changes/polynomial-colimit-functor.md`. The consumer import adaptation is described below. Profiling options are removed from the delivered file. The complete module
compiled cleanly through `lcompile.py` in 42.8 seconds.

The proof tests empty and infinite generator sets uniformly: the polynomial
universal property and categorical product universal property impose no nonempty
or finite assumptions. The zero target ring and non-surjective augmentations also
require no extra hypothesis. The unit route and all declared proof dependencies
are retained.

## Proved and sorry left

Closed the sole original hole:
`Algebra.PolynomialHomology.computationData_exists`
(node `lem-trf-polynomial-presentation-homology`).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in the delivered module.
The adapted consumer retains its existing hole
`Algebra.PolynomialSquareBar.data_nonempty`
(node `lem-trf-polynomial-square-bar-naturality`), unchanged and not added by this packet.
All private helpers are proved. `ComputationPackage` contains data and proof fields,
with no hollow definition or new assumption. The general derived comparison is used through its
existing `Computation` parameter, as required by the original statement.

## No longer needed

Removed public import `Sheaf.AlgebraicTopology.TrivialKanFibration`, which current
preflight lists as route-pivot dropped. The returned landing additionally requires
`Sheaf.RingTheory.PolynomialSquareBarNaturality` to retain access to that alias, so
the consumer initially received exactly that direct public import. Compilation passed,
but preflight refused the import as route-pivot dropped. The repair therefore imports
Mathlib directly and expands the reducible alias at all three consumer use sites.
All elaborated types stay identical; neither delivered module needs the dropped alias module. Its reducible alias
`SSet.Enhanced.trivialKanFibration` is replaced by its exact Mathlib definition
`SSet.modelCategoryQuillen.I.rlp`, imported from
`Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`. The definition node
`def-weil-pbc-trivial-kan-fibration` remains needed as this Mathlib leaf. No modules
are withdrawn, and all other declared dependencies remain needed. Exploratory imports of `Mathlib.CategoryTheory.Limits.Types.Pullbacks` and
`Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks` were removed: existing
imports already expose the APIs used by the proof.

Searches: LeanFinder found general simplicial colimit and cofibrant-resolution
interfaces but no polynomial presentation comparison. Loogle found
`MvPolynomial.eval₂Hom`, `MvPolynomial.eval₂Hom_C`, `MvPolynomial.eval₂Hom_X'`
and polynomial extensionality, used directly. Mathlib grep for
`polynomial.*simplicial|simplicial.*polynomial|derived.*colimit` found only
`HasPointwiseRightDerivedFunctorAt.hasColimit`, which concerns pointwise right
derived functors and does not prove this assertion. Repository searches found no
existing duplicate theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy or statement change. The inherited item imported a
module rejected by the current route-pivot gate; its exact Mathlib alias expansion
repairs this without changing the trivial-Kan hypothesis. The DAG's six proof steps are
implemented as written. The concrete record's generated kernel checks required the
implementation repairs documented above; all six conditions remain verbatim.
The original downstream check preceded the arrival of
`Sheaf.RingTheory.PolynomialSquareBarNaturality`; the returned landing identified
its dependency on the formerly re-exported alias. The requested direct public import compiled but was rejected by the route-pivot gate.
Replaced it with the direct Mathlib import and the three exact reducible-alias
expansions; all other consumer text is unchanged. The consumer is currently unclaimed. See
`coord/changes/polynomial-square-bar-trivial-kan-import.md`.
No new mathematical lemma nodes or proof dependencies are introduced.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
