## What changed

Proved `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`
with its entire existing signature unchanged. The proof imports the already proved
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` theorem
`boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`. It extracts the existing
invertible-exponent class, converts the cohomology predicate and boundedness, applies that
source theorem, and converts back. The output interval is normalized with min and max.
All three public imports and every definition and statement are unchanged. No change record
or consumer adaptation is needed for the two private proof imports. Updated the item's DAG
proof, proof dependencies and proof origin to describe this source reuse.

The single module compiled through lcompile.py in 5.4 seconds, without diagnostics.
The source proof was read: its separated case uses open/proper compactification, and its
nonseparated case inducts on a finite affine cover using localization triangles. The unit
record `sk-prop-sf-cbc` has empty realized statement/step lists, so no mandated realized node
is bypassed. The proof does not use the still-holed, similarly named generic theorem in
`Derived.Stability.DirectImage`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`
(node `thm-dg-finite-type-constructibility`). Added 0 holes. Split off 0 statements.
No sorry remains in the delivered Lean module. This reuses a proved source theorem;
no assertion is made that its entire dependency closure is already free of sorry.

The signature retains arbitrary finite-type morphisms (no separatedness assumption), the
original universe and coefficient hypotheses, and the ordinary derived direct image.
The conversions work for the zero coefficient ring, zero complex, empty source and empty
target. The min/max interval also handles unordered source bounds for a zero output.

## No longer needed

Removed the following private proof imports from this wrapper:

- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.Compactification.Affine`
- `WeilConjectures.Compactification.Defs`
- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.Algebra.Homology.FiniteStripAugmentation`

The source theorem replaces the proposed explicit injective Cech bicomplex, totalization,
finite filtration and page argument in this wrapper. The following former direct DAG
proof dependencies are removed (the underlying mathematical results may still be used
inside the reused source proof or by other modules; no global unreachability is claimed):

- `lem-wf-affine-noetherian-components`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-pur-kinjective-restrict-localized-adjunction`
- `def-weil-pbc-direct-image`
- `prop-nagata-affine-compactification`
- `def-nagata-affine-compactification`
- `def-nagata-compactification`
- `cor-fin-deligne-open-finite-coefficients`
- `lem-fin-proper-bounded-constructible`
- `lem-weil-derived-direct-image-composition`
- `lem-dg-etale-injective-finite-cech-rows`
- `def-sp-double-complex-total`
- `lem-sc-finite-strip-row-augmentation`
- `lem-sp-bounded-filtered-page-core`
- `thm-constructible-serre`

Removed all nine former top-level tool-use entries, since the wrapper does not directly
invoke those tools. The coefficient convention, bounded-constructible definition and
finite-module constructibility comparison remain. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan overlooked the already proved source declaration
`boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType`, which has exactly the
required finite-type generality after the known predicate conversion. It is acyclic to
import: import_direction.py confirmed that its module does not reach this item. There is
no statement defect and no change to the targets or coefficient/derived definitions.

Searches actually run: LeanFinder for derived direct image bounded constructibility over
a field returned eight unrelated Mathlib geometry results; Loogle for
`"boundedConstructible"` returned no hits; msearch grep for
`boundedConstructible.*rightDerivedLowerStar` returned no Mathlib hits. Repository rg found
the source theorem, whose signature and complete proof were read before use. The existing
long declaration docstring records the original mathematical Cech proof; the updated DAG
and this report record the shorter Lean implementation by source reuse.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
