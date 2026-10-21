## What changed

Replaced the hole in `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_scalarExtension`
by a counit-transpose proof. Three proved private helpers express the composition
theorem in the exact comparison notation, give the scalar-mate counit formula for the exact derived
adjunction, and establish the scalar/pullback square. The latter
uses `AlgebraicGeometry.Etale.scalarPullback_composition` on the two paths, expands
the specified square comparison, and cancels the common composition isomorphism.
The main proof applies the final adjunction Hom bijection, rewrites naturality and
mate/counit equations, and postcomposes that square identity with the scalar image
of the geometric counit.

Added private proof imports of `Sheaf.Paper.ScalarPullbackComposition`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` and
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`.
Updated the existing node's proof route and proof dependencies.
The import-pruning change record is
`coord/changes/D6-etale-scalar-exchange-import-pruning.md`. The node statement,
Lean attachment, target signatures and unit route are unchanged. The newly cited
`lem-sf-scalar-pullback-composition` is a generic composition coherence tool from
another unit; its use replaces the previously approved generic normalization tool.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_scalarExtension`
(node `lem-pur-etale-direct-image-scalar-exchange`), the module's sole original hole.
Added: none. Remaining holes in delivered Lean files: none. The proof uses the
existing stated theorem `AlgebraicGeometry.Etale.scalarPullback_composition`, whose
own proof is still `sorry` in its existing module; no transitive
axiom-freedom claim is made here.

Validation: `lcompile.py` compiled the complete module cleanly in 8.5 seconds.
The required `deliver3.py` additionally runs server compilation, the axiom and
statement checks, and the delivery preflight before pushing. Import-direction
checks permit both new project proof dependencies, and the specialized
composition dependency closure (412 nodes) does not reach this item.

## No longer needed

The direct proof dependency `lem-sfb-kflat-scalar-comparison-normalization`
(module `Sheaf.Paper.KFlatScalarComparisonNormalization`) and the direct use of
`prop-weil-pbc-inverse-image-modules-exact` are unnecessary: the existing
small-etale composition theorem already states the exact comparison needed.
The node's obsolete normalization tool approval is removed; no DAG node or module
is withdrawn, and those results may remain needed by other consumers.

Removed redundant direct public imports:
`WeilConjectures.AlgebraicGeometry.DerivedCategories`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
Only the chosen square, exact exchange and coefficient comparison imports are
needed for the public statement. No module is claimed globally pruned merely
because its direct import was removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's first step can use the already stated specialized scalar/pullback
composition identity instead of constructing and transporting the generic
ringed-module normalization. The remaining counit argument is unchanged.
The exactness transport of the scalar-mate counit needs the proved identity
`mapDerivedUpperStarLowerStarAdjunction_eq`; the proof includes it explicitly.
No statement repair, new node, definition change or forced consumer adaptation
is needed. Edge cases (identity maps, empty schemes, zero coefficients and
nonflat coefficient maps) use exactly the same categorical identities, with
no cancellation except of specified isomorphisms.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
