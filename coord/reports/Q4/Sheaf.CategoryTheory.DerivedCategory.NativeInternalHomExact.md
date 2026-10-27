## What changed

Proved `DerivedCategory.nativeInternalHom_contravariant_exact` without changing its signature.
Specialized the existing signed bifunctor-Hom homotopy exactness theorem to the native
internal-Hom bifunctor. Its complex is definitionally the native internal-Hom complex;
precomposition agrees by the product projection formulas. Constructed the natural
K-injective comparison on the homotopy category, descended coherent shifts along `Qh.op`,
and transported triangulatedness using essential surjectivity on arrows.

Added private proof imports of
`Sheaf.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExact`,
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated`, and
`Mathlib.CategoryTheory.Triangulated.Opposite.Functor`. Updated the existing DAG node to
record this specialization and localization argument. No source-library file, public
signature, public import, definition used by a target, or instance visible to consumers changed.

Validation: the complete module compiled cleanly through `lcompile.py` in 7.5 seconds,
with no warnings or errors. The import-direction check found no cycle.

## Proved and sorry left

Closed 1 hole: `DerivedCategory.nativeInternalHom_contravariant_exact`
(node `lem-weil-native-internal-hom-contravariant-exact`).

Added 0 holes; split off 0 statements. The item contains 0 remaining `sorry`s.
The existing theorem
`CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact`
(node `lem-sf-bifunctor-homotopy-exact`) is used as a declared dependency; its existing
hole is unchanged and no copy or replacement of it is introduced.

## No longer needed

Removed the unused private helpers `cochainSourceShift` and `sourceShiftSign_add`.
Removed their proof imports `Mathlib.CategoryTheory.Shift.Adjunction`,
`Mathlib.CategoryTheory.Adjunction.Unique`, `Mathlib.Algebra.Ring.Int.Parity`, and
`Mathlib.Tactic.Ring` (some remain available transitively).

The item no longer performs separate raw reindexing, quadratic-sign coherence, or
split-sequence connecting-arrow calculations: those are supplied by the existing
generic exactness node `lem-sf-bifunctor-homotopy-exact`. No previously declared
proof dependency is removed: both `def-weil-abstract-derived-category` and
`def-sp-grothendieck-abelian` remain needed. No library module is withdrawn or declared
unreachable; in particular all dependencies of the generic exactness theorem remain.

## Where the brief, the DAG or earlier work was wrong

The earlier item plan predated the generic signed bifunctor-Hom exactness statement.
Its differential agrees exactly with the native complex, so repeating the full signed
cone calculation here is unnecessary. The existing `exists_distinguished_ihom_pre`
only produces some third arrow; the proof therefore uses the coherent generic exactness
theorem and transports its shift structure, preserving the actual triangle maps.
The unit route is unchanged. No statement or definition repair was needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
