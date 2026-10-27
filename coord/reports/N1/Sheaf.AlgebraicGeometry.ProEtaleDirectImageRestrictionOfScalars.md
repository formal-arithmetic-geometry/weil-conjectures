## What changed

Filled both proofs in `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`.
All existing public declaration signatures, attributes, definitions, instances and public
imports are unchanged. No other existing Lean module is changed.

The underived proof specializes the already-proved ring-sheaf coefficient comparison.
Naturality of sheafification proves the constant-section coefficient square; taking
adjoints gives the inverse-image square. The adjunction triangle identifies the generic
ring structure maps with the canonical maps used by this module. Private helpers
parameterize the two structure maps before substituting these equalities, preserving
the dependent module actions and identity-on-sections characterization.

The derived proof specializes the already-proved, unit-normalized ring-sheaf comparison.
Its normalization makes the A-derived unit on the restriction of a K-injective B-complex
invertible. Naturality at a K-injective A-resolution then shows that direct image sends
that resolution map to a quasi-isomorphism. Inverting the comparison and cancelling the
K-injective units proves exactly the published normalization for every resolution map.
No preservation of K-injectivity by scalar restriction is assumed.

Added one private proof import, `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
for the canonical constant-ring inverse-image isomorphism. Private derived-category
abbreviations specify the existing standard localization and universe parameters;
they introduce no new category or chosen data.

Updated the existing node
`lem-weil-proetale-direct-image-restriction-of-scalars` in its `proof` and
`proof_origin` fields to include this canonical constant-ring specialization. The node
also records the separate fixed-scalar presentation, so its earlier proof and dependency
lists are retained. Its statement, Lean attachment and unit route are unchanged.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Scheme.proEtaleCoefficientDirectImageComparison_existsUnique`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedDirectImage_restrictScalars`.

Both belong to `lem-weil-proetale-direct-image-restriction-of-scalars`.
There are zero remaining holes in the item and zero holes added anywhere. All private
helpers are proved. No split-off statements or new axioms are introduced.

Validation: the complete item compiled cleanly through `lcompile.py` in 37.7 seconds,
with no errors or warnings. A textual check confirms all six original public signatures
are identical; the node proof dependencies equal the union of its proof-step uses.

## No longer needed

Removed these redundant direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `Mathlib.Algebra.Category.Grp.AB`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`.
- `Mathlib.Algebra.Category.Ring.Limits`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.

The generic comparison and its public dependencies already supply the module-category,
exactness, derived-functor and K-injective APIs. This specialization does not directly
invoke the separate exact-functor-derived-functor theorem, compose two ringed-topos
derived comparisons, or choose a second K-injective resolution over Y. It uses the
normalized comparison in `lem-weil-pbc-ring-sheaf-change-adjunction` instead.

No whole module is withdrawn and no DAG dependency is claimed globally unnecessary:
the existing node also realizes the fixed-scalar presentation, which still uses its
recorded scalar-model route; some removed direct imports also remain transitive
dependencies of the generic coefficient comparison.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing generic ring-sheaf comparison already
contains the required derived square and normalization, giving a shorter specialization
than reconstructing the two-factorization argument in the item's old docstring.
The canonical and generic direct-image structure maps are propositionally equal by the
adjunction triangle, rather than definitionally equal. Substituting their equalities in
a helper parameterized by both structure maps handles the dependent section types.
The revised docstring and node explicitly describe this route while retaining the
node's separate fixed-scalar proof. No definition repair, consumer adaptation, change
record or new node is needed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
