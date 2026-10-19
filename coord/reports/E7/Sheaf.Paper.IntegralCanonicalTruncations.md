## What changed

In `Sheaf.Paper.IntegralCanonicalTruncations`, proved ambient truncation membership,
the complete cohomology/additivity/distinguished-triangle package, and exact countable
products. The membership proof uses the existing proof-only import of
`IntegralStratifiedPerfectCharacterization`; added a proof-only import of the source
library's derived-category `TStructure` module. Existing signatures,
definitions, visibility, hypotheses, universes and the unit route are unchanged.

Membership uses `integralStratifiedPerfectClosure` directly, after deriving global
invertibility of the integer l from stalkwise invertibility. The properties theorem
uses actual ambient truncation maps: lower truncation is truncLT(m+1), so its cohomology
map is invertible through degree m; upper truncation retains degrees at least m+1.
The vanishing statements and distinguished triangle are the standard ambient ones.
Additivity is checked on underlying morphisms of the full subcategory.

For countable products, the product-of-epimorphisms clause of
`ProEt.countableProducts_exact` supplies preservation of epimorphisms by the product
functor. Its canonical comparison with the limit of a discrete diagram identifies
this product map with `lim.map`. Exactness follows from the abelian criterion, and
exact limits of shape Discrete Nat give CountableAB4Star. The construction explicitly
provides the finite biproduct instance needed by that criterion.

Compiled the module through lcompile.py while developing these proofs. On resumption,
the retained module was compared with the current shared source and compiled cleanly
against the current server library in 3.8 seconds (exit code 0). The required initial
dry run was started before further work. No new statements or nodes were added.

## Proved and sorry left

Closed three of the original six holes, with no holes added:

- `AlgebraicGeometry.Scheme.pbcIntegralCanonicalTruncations_mem`.
- `AlgebraicGeometry.Scheme.pbc_integral_truncation_properties`.
- `AlgebraicGeometry.Scheme.pbcCompletedCountableAB4Star`.

The following three original holes remain unchanged, all attached to
`thm-weil-pbc-integral-truncations` and retaining their source and proof docstrings:

- `AlgebraicGeometry.Scheme.pbc_flat_cohomology_torCompatible`: needs generic
  completed scalar-extension cohomology and flatness transport for an arbitrary datum.
- `AlgebraicGeometry.Scheme.pbc_torCompatible_iff_flat_cohomology`: needs the all-level
  Tor/flatness criterion transported from the dependency's unlifted valuation-ring
  convention to this module's ULift coefficient convention, and the identification
  of degree-zero K-flatness with flatness.
- `AlgebraicGeometry.Scheme.pbc_integral_truncations`: needs coherent truncation
  comparisons for canonical reduction diagrams, transport of complete-object
  reconstruction across the actual tower interfaces, and the normalized counit/unit
  equations. The existing dependency interfaces use strict derived towers or
  representative Roos triples, rather than this module's evaluated diagram directly.

This is a partial proof delivery, not a decomposition. Zero split-offs.

## No longer needed

The completed proofs do not need these proof-only imports from the current shared module,
so they are absent from the delivery:

- `Sheaf.Paper.FiniteReductionReconstructionCompleted`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `Sheaf.Paper.AdicCoefficientDatum` (already available through public dependencies).
- `Sheaf.Paper.BoundedConstructibleTower` (already available through public dependencies).
- `Sheaf.Paper.CompletedRlimFunctor`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.IntegralUniformCoefficient`.
- `Sheaf.Paper.KoszulReconstruction`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.

The remaining three holes retain their original proof plans; in particular reconstruction,
scalar-change and Tor-flatness nodes may still be needed for them. This partial delivery
therefore claims no DAG node or module globally unnecessary. No public imports removed,
and no modules withdrawn. `IntegralStratifiedPerfectCharacterization` remains imported
because the membership proof uses its standard-truncation closure theorem.

## Where the brief, the DAG or earlier work was wrong

The membership docstring described reconstructing local kernels and models even
though the existing `integralStratifiedPerfectClosure` already states the exact
closure needed. Its docstring now records the direct proof. The other original
proof plans are retained for the unchanged holes.

The shared checkout initially lacked the assigned file while the node still named
it; the file appeared during inspection and was copied normally. No repository
files or launcher scripts were changed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
