## What changed

Proved `CategoryTheory.Functor.normalizedDerivedComparison_composition` in
`Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition`. Both public definitions,
the theorem signature, all universe parameters, and both public imports are unchanged.
All added helpers are private and proved.

The proof transports the existing derived unit to complexes, derives the unit square
from the supplied normalization, and extends that square to every complex by naturality.
It pastes the two unit squares using the canonical localization composition maps.
At a K-injective complex the normalization makes the relevant source unit invertible,
so cancellation proves equality. Naturality along a K-injective resolution and
localization extensionality give equality at every derived object.

Updated the item's DAG proof, proof dependencies, and proof origin to this argument.
No other module or declaration interface changes. The first preflight requested a
change record for the added section variables and local attribute. Their scopes,
unchanged signature, and consumer check are recorded in
`coord/changes/t9-normalized-derived-comparison-private-context.md`.

## Proved and sorry left

Closed one hole: `CategoryTheory.Functor.normalizedDerivedComparison_composition`
(node `lem-sf-normalized-derived-comparison-composition`). Added zero holes and split
off zero statements. The item contains zero `sorry`s, including its private helpers.

Verification: the complete module compiles cleanly through `lcompile.py` (33.9 s).
`#print axioms CategoryTheory.Functor.normalizedDerivedComparison_composition`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`. A source comparison
confirms that the public theorem signature and both public definitions are unchanged.

## No longer needed

The proof does not invoke `normalizedDerivedComparison_commonResolution` or any
of the theorems of `KInjectiveDerivedMapComputation`. Removed the corresponding
proof-dependency edges to `lem-sf-normalized-derived-comparison-common-resolution`
and `lem-sf-kinjective-derived-map-computation`. The latter remains a statement
dependency: the normalization still uses its canonical resolution comparisons.

No imports or modules are removed. The public common-resolution import still supplies
the two identification definitions used by the normalization's public signature.
The exact-functor import supplies the canonical localization composition isomorphism.
No globally unused module is claimed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The initial preflight's sole
refusal was the missing change record for private proof context commands; the record
has been added without changing the compiling proof. The DAG's successive-resolution
argument is valid but unnecessary: naturality of the derived unit extends the
normalization to all complexes before pasting, avoiding a second resolution in the
intermediate category. The unit record has no realized proof steps bypassed by this
change. No preservation of K-injective complexes is assumed anywhere.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
