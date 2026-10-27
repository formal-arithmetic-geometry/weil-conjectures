## What changed

Decomposed `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1SingleLevelTriangles` into
exact singleton construction and unconditional comparison of composite words, then wrote
the remaining reflection argument in Lean. The item theorem and every existing public
signature remain unchanged.

`TowerP1SingleLevelData` contains the original ten interfaces with the same names, types
and bodies. The original module publicly reexports this module. This prevents an import
cycle when the two new proof items use those interfaces; it is not a compile-time split.
The change record is `coord/changes/W4-single-level-interface-extraction.md`.

The complete main proof substitutes the singleton images in the two assumed tower
identities, evaluates them, cancels the specified invertible comparison components, and
reflects equality with bounded-below comparison faithfulness. The private helper
`nu_map_injective` proves reflection using the fully faithful bounded-below comparison
and the derived realization equivalence. The private helper `nu_plus_of_origin` proves
the required lower boundedness from the retained origin of FJ or GJ. Thus the proof does
not silently apply bounded-below faithfulness to an arbitrary unbounded object.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1SingleLevelTriangles`
(node `lem-sp-tower-p1-single-level-triangles`), by a complete proof from two strictly smaller
statements. This is a decomposition, not a net hole reduction: 1 original hole closed,
2 new holes added, 0 holes left in the item module, 2 holes left in the delivery.

The new holes, each with proof exactly `:= by sorry`, are:

- `AlgebraicGeometry.ProEtale.SpTowerP1.singleLevelConstruction`, node
  `lem-sp-tower-p1-single-level-construction`: exact zero-off-n embeddings and normalized
  natural operation comparisons. It asserts no triangle identity.
- `AlgebraicGeometry.ProEtale.SpTowerP1.singleLevelTransport`, node
  `lem-sp-tower-p1-single-level-transport`: unconditional commuting squares for both
  composite words. It assumes no tower identity and concludes no triangle identity.

Both private helpers have complete proofs. The extracted interface module has zero holes, as did
the original interface definitions. No data is defined by choosing a witness of either
new theorem. Every new hole has its source and detailed proof in its docstring and node.

## No longer needed

Removed the original private imports `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`, `Sheaf.Paper.SemilinearDerivedSections`,
and `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` from the extracted interface
module: the retained public dependencies already supply its definitions and exactness API.

The main theorem now directly needs only the construction node, the transport node and
`sk-prop-sf-comparison`. Its former proof dependencies
`sk-def-sp-coefficient-towers`, `det-sp-coefficient-towers-abelian`,
`def-weil-pbc-site-comparison-morphism`, `lem-weil-pbc-site-pullback-abelian-exact`,
`lem-sf-exact-functor-derived-triangulated`, `def-weil-pbc-etale-origin-witness`,
`lem-coef-semilinear-derived-sections`, and `lem-sp-tower-p1-etale-origin-comparisons`
remain needed by the construction, transport or unchanged interface; they are not claimed
as globally pruned. No mathematical node or module is withdrawn; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The existing lower singleton extension functors
are not substitutes for this construction: they use scalar extensions at lower levels,
whereas this interface explicitly requires zero at every level other than n. The assigned
DAG's elementary description of the composite-word identification hides substantial
naturality and origin-transport glue. That glue is now a separate unconditional statement.

Checked edge cases in the new statements: n=0 (the first positive coefficient level),
the zero complex, the empty scheme, shifted inputs, and non-flat finite modules. Zero
adjacent transitions remain semilinear in each case. No normalized tower, transition-
compatible origin family, finite-Tor condition or extra geometric hypothesis is introduced.
The construction theorem is only an existence proposition used inside another proof; it
does not define data by arbitrary selection from an unproved existence theorem.

## New nodes

`def-sp-tower-p1-single-level-data` attaches the unchanged interfaces extracted to
`Sheaf.Paper.TowerP1SingleLevelData`. Its definitions have real bodies and no holes.

`lem-sp-tower-p1-single-level-construction` isolates original proof steps 1--3, sourced
from the Levels paragraph: construct zero-off-n systems, localize the exact comparison
composite, and assemble normalized push/pull isomorphisms. It is strictly smaller than
the conditional triangle theorem because it proves no identity or reflection.

`lem-sp-tower-p1-single-level-transport` isolates original steps 3--4: compare the actual
composite words before imposing any triangle identity. The main proof supplies the
identity substitution, boundedness argument, cancellation and faithful reflection.

Blueprint searches for single-level and triangle words found no imported duplicate.
LeanSearch returned generic homological-functor and truncation declarations; LeanFinder
returned constant-sheaf and condensed comparison declarations; Loogle identified generic
faithful-functor injectivity lemmas. The Mathlib/source grep found no exact construction
or normalized composite-word comparison. Existing unrelated singleton extensions were
read and excluded for the lower-level reason above. These are recorded as no match,
not as claims that generic supporting theory is absent.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
