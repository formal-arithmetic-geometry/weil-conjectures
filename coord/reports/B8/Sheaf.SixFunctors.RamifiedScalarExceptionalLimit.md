## What changed

Reduced `WeilConjectures.RamifiedScalarExceptionalLimit.ramifiedScalarExceptionalLimit`
without changing its statement or `Realization`. The proof obtains normalized preparation,
constructs all five functor isomorphisms by whiskering and composition, proves their specified
component formulas, and applies the separate proper/open support square. In particular, source,
target, scalarY, supportSource and supportTarget are actual definitions with complete bodies;
none is selected from an existence theorem or filled by sorry. Explicit functor associators
and a separate scalar-system comparison avoid expensive kernel conversion of long composites.

Added `Sheaf.SixFunctors.RamifiedScalarPreparation` and
`Sheaf.SixFunctors.RamifiedScalarSupportCompatibility`. The first isolates normalized system,
scalar, adjunction, cofinal and Tor data before the five limit realizations. The second asserts
only the ordered proper/open support-comparison square for those explicitly constructed maps.
Updated the parent proof route and added a node for each remaining theorem.

## Proved and sorry left

One original hole closed:
`WeilConjectures.RamifiedScalarExceptionalLimit.ramifiedScalarExceptionalLimit`
(lem-coef-ramified-scalar-exceptional-limit).

Two holes added, each the whole proof of a named public theorem:

- `WeilConjectures.RamifiedScalarPreparation.existsPreparation`
  (lem-coef-ramified-scalar-preparation).
- `WeilConjectures.RamifiedScalarSupportCompatibility.supportComparison`
  (lem-coef-ramified-scalar-support-compatibility).

This is a decomposition, not a net hole reduction: one closed, two added. No sorry remains
in the item module. The preparation omits the five limit isomorphisms and their component
normalizations, which the delivery constructs and proves; the support square is a separate
proper/open identification and contains no existential reconstruction or exceptional transpose.

## No longer needed

The item no longer directly imports `Sheaf.Paper.IntegralResidueTor`,
`Sheaf.Paper.NormalizedDVREffectivity`, `Sheaf.Paper.PurAdicScalarExtensionTorBound`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Paper.SfIntegralCompactSupportConstructible`,
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`, or
`Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`.
Their mathematical obligations remain below the normalized preparation and support square;
this is not a claim that these nodes can be withdrawn. No existing module or declaration is
withdrawn, and no unit step is bypassed. Existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies contain the underlying mathematical ingredients, but their
published Lean interfaces do not directly construct this simultaneous `FiniteScalarMate.Context`
and its normalized integral/system adjunction comparisons. The adopted integral exceptional
statement is presented on the small etale site, while this item uses the specified completed
pro-etale coefficient systems. The preparation records that interface work explicitly.

The current blueprint moved the scalar-six argument to
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/`;
the older source path in the parent node is absent from the latest snapshot. The new nodes cite
the current compact-support and exceptional proof paragraphs. No mathematical statement was
changed or marked disputed. Edge cases checked in the reduction: zero input, empty schemes,
identity coefficient extension, e=1, and equal quotient indices. Compositions use the actual
counits and completion units; no finite-evaluation faithfulness is used.

## New nodes

`lem-coef-ramified-scalar-preparation` records the normalized scalar/system and adjunction
preparation (parent steps 1--3 and support-unit normalization), with its specified constructible
domains and uniform Tor intervals. The same module defines the five resulting limit
isomorphisms by complete Lean expressions.

`lem-coef-ramified-scalar-support-compatibility` records parent step 6 for those constructed
support isomorphisms. Its conclusion is only the proper/open comparison square; all the
existential and exceptional-limit work lies outside this theorem. Both nodes inherit the
parent's chapter/unit and cite its blueprint ancestor. No change record is needed: no existing
statement, definition or public import changed.

Validation: all three modules compiled through lcompile.py. The item module has no
sorry; the two split theorems are its only new holes. The parent Realization declaration
was compared against the shared source and is unchanged.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
