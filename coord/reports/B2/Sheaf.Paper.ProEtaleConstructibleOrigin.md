## What changed

Proved both admitted theorems in `Sheaf.Paper.ProEtaleConstructibleOrigin`, with every
existing signature and public definition unchanged. Added only private, fully proved helpers.

The constant-ring comparison is invertible because forgetting commutativity preserves local
bijectivity and hence sheafification. Its sheafification-unit equation gives the scalar
compatibility needed to construct the canonical realization unit. The unit is an isomorphism
on underlying additive sheaves. This identifies the recorded coefficient presentation with
fixed-module-valued sheaves, and identifies their exact derived comparisons.

The constructible-sheaf equivalence reuses the existing fixed-module origin theorem. For
complexes, `fixedDerivedOrigin` applies the source's `DerivedCategory.prop_of_bounded` to the
triangulated essential image of the fully faithful bounded-below comparison. Exact comparison
commutes with cohomology and reflects vanishing; the existing sheaf origin theorem and full
faithfulness reflect constructibility. The lifted complex is therefore bounded constructible.
The coefficient equivalence transports this argument to the recorded derived category.
The proof constructs the required full-subcategory equivalences and natural isomorphisms,
and proves the equality of intrinsic and etale-origin object properties by both inclusions.

Read Stacks `proetale.tex`, labels `lemma-compare-constructible` and
`lemma-compare-constructible-derived` (Tags 09AK and 09AL), and the existing source proof
of bounded devissage in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
No global-stratification convention is replaced by an affine-local one. Empty schemes,
empty strata, zero coefficient rings and arbitrary bounded intervals remain included.

Updated the existing node's proof, proof dependencies and proof origin to follow this route.
No new module, definition repair, statement change, or consumer adaptation is needed.
The existing node's unit record has no realized statement or steps to bypass.

Validation: the complete sandbox module compiled through `lcompile.py` with exit code zero
against the current compiled library in 11.1 seconds and no diagnostics. Delivery preflight supplies the independent mechanical gates.
Several earlier compiler requests received no server answer; retrying succeeded.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.ProEtale.isIso_originConstantRingComparison`.
- `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`.

Both belong to node `lem-sf-proetale-constructible-origin`. No `sorry` remains in the module,
and none was added elsewhere. This is a proof from existing declared dependencies, not a
new decomposition. Existing dependencies may themselves still use admitted theorems.

## No longer needed

Removed the following proof imports:

- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`: its fixed-module source theorem is used
  directly, and the coefficient identification needed here is constructed explicitly.
- `Sheaf.Paper.ProEtaleLisseOrigin`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`.
- `Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum`.
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.

The three Mathlib modules are no longer direct imports: the generic derived and triangulated APIs are
provided by the source modules used in the bounded-devissage proof. The additional
comparison, localization and inverse-image modules are not used by this route;
existing public imports already expose the bounded constructibility and derived
category definitions used in the unchanged signatures.

The original node's proof no longer directly needs these nodes:

- `def-weil-pbc-site-comparison-morphism` (the comparison interface is already imported).
- `lem-weil-pbc-comparison-pullback`.
- `lem-sf-proetale-locally-constant-origin`.
- `def-weil-proetale-constructible-sheaf` (still a statement dependency).
- `prop-weil-pbc-site-comparison-finite-level`.
- `lem-cbc-proetale-stalk-conservative` (still a statement dependency).
- `lem-sf-derived-ses-triangle`.
- `def-weil-triangulated-category`.
- `lem-sf-triangle-morphism-iso`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-constructible-partition-local-closed-stratum`.
- `def-weil-proetale-inverse-image`.
- `lem-sf-proetale-open-closed-sequence`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `prop-weil-pbc-comparison-direct-image`.
- `def-weil-pbc-derived-categories`.

The geometric sheaf descent argument is already implemented by
`lem-weil-pbc-fixed-module-constructible-origin`; the bounded-devissage API implements
truncation induction. These removals describe this proof's direct dependencies, not a claim
that the removed nodes have no other consumers or transitive uses.

## Where the brief, the DAG or earlier work was wrong

The nine-step proof plan repeats a sheaf descent argument already available in the source
library and a finite-amplitude induction already available as `DerivedCategory.prop_of_bounded`.
Reusing those declarations removes that duplicated work. The intrinsic and etale-origin
object properties also use the same `Stratification`, whose data already include
constructibility of all strata; the extra constructibility conjunct in the origin predicate
is redundant and is supplied or discarded explicitly, without changing either definition.

The reused fixed-module origin and encoding nodes are tools from the proper-base-change unit;
they provide the existing coefficient interfaces needed by this unit's comparison theorem.
No tool approval field was added or modified by this delivery.

The etale constructibility comparison is used through its existing source-library
version `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`, whose statement
and proof coincide with the recorded side-library comparison. No duplicate theorem
is added. The existing declaration docstrings are retained; the node records the actual five-step route.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
