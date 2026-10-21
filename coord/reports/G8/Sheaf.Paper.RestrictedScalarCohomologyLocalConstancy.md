## What changed

Proved `AlgebraicGeometry.Scheme.restrictedScalarCohomology_finiteLocalModels` along
its original restricted-tensor and finite-action route. Its signature and
`SheafOfModules.constantCoefficientScalarExtensionOfUniverses` are unchanged.
All original public imports remain verbatim.

Added four proved bridge modules, each with its own node:

- `RestrictedScalarTensorCohomologyComparison`: the K-flat counit and the existing
  independent-coefficient tensor comparison identify underlying scalar-extension
  cohomology with intrinsic tensor cohomology. Exact forgetting compares both
  localization universes with cochain homology. Canonical coefficient pullbacks
  have the same underlying set inverse image.
- `RestrictedScalarCoefficientLocalConstancy`: the actual ring sheafification
  unit identifies the restricted regular coefficient with the constant A-module B.
  Uniqueness of the constant/pullback left adjoints and the single-complex
  homology calculation give the tensor input.
- `ProEtaleFiniteUnderlyingModels`: the intrinsic/fixed coefficient comparison
  and finite stalks give finite models; base change supplies them on every object.
- `ProEtaleFiniteActionLocalModels`: specialize the existing finite-action theorem
  and compare its restricted global constant models with the localized constants
  in the target predicate.

Updated the item's proof, proof dependencies and proof origin. No existing
statement, definition, source-library declaration, target or unit route changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.restrictedScalarCohomology_finiteLocalModels`.

Added zero holes. The four new public bridge theorems are proved:
`restrictedScalarTensorCohomologyComparison`,
`restrictedScalarCoefficient_finiteLocalConstancy`,
`proEtale_finiteUnderlyingModels_of_locallyConstant`, and
`proEtale_finiteLocalModels_of_finiteUnderlying`.
Every private helper is proved. There is no `sorry` in the delivered Lean files.
The four bridge modules compiled without warnings on the server through
`lcompile.py`; each took between five and eight seconds.
The proof uses the existing named dependency declarations, including the
restricted tensor local-constancy theorem and the unit-normalized inverse-image
comparison; any existing holes in those declarations are unchanged.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, replaced by
  the existing maximum-site-universe specialization `KFlatResolutionGeneral`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`; the
  restricted tensor theorem uses the intrinsic tensor, not that fixed-module tensor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`; the new coefficient
  and comparison modules expose the required constructions.
- `Sheaf.Paper.ProEtaleConstantModulePullbackHomology`; it is available through
  the new comparison module and is still used.
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`; the actual
  constant-scalar pullback encoding supplies the required constant-model comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`; the existing proved
  intrinsic/fixed finite-model comparison supplies finiteness directly.
- `Sheaf.Paper.RestrictionDerivedProducts`; exact forgetting to abelian sheaves
  compares cochain homology without a derived scalar-restriction functor.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`; use the existing
  unit-normalized underlying-set comparison for the actual intrinsic inverse image.
- `Sheaf.CategoryTheory.FiniteRingActionLocalConstancy`; it remains used by the
  new finite-action bridge.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`; the existing proved
  finite-model comparison handles the slice and geometric-point work.

`ProEtaleBoundedConstructibleTriangulated` remains as a private `import all` to
use its proved isomorphism-transport helper. The old direct dependencies
`lem-sfb-geometric-inverse-image-constant-module`,
`lem-weil-proetale-constant-sheaf-stalk`,
`lem-weil-pbc-restriction-derived-products`,
`lem-pe-constant-left-module-inverse-image`, and
`lem-weil-proetale-weakly-etale-localization` are replaced in the item's route by
the explicitly proved bridges. Obsolete corresponding `tool_uses` entries are
removed; the coefficient-comparison entry is also encapsulated in the new bridge.
These are direct-route removals, not requests to withdraw declarations or modules
that other proofs still use. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Two presentation details needed explicit
Lean comparisons: the intrinsic tensor uses the standard localization universe,
whereas the item allows independent chosen source and target universes; and the
finite-action theorem's models are restrictions of global constant modules,
whereas the target predicate constructs constants directly on the slice.
The proof preserves these distinctions and supplies the isomorphisms.

The new statements include empty schemes and empty covering members. The tensor
comparison assumes no flatness of B over A, so includes Z/4 → F₂. The coefficient
complex is zero away from degree zero, including when B is the zero ring. The
model conversions preserve the finite model rather than imposing one common cover
for all cohomological degrees. These edge cases introduce no extra hypotheses.

The `def-weil-derived-tensor` attachment currently points to the fixed-module
source tensor. The declared restricted-tensor theorem actually uses the existing
intrinsic construction in `Sheaf.Algebra.Homology.DerivedTensor`. This delivery
uses that construction without changing the definition node or the source tree.

## New nodes

`lem-sp-restricted-scalar-tensor-cohomology-comparison` records the K-flat
underlying cohomology and actual pullback comparison, without finiteness or bounds.

`lem-sp-restricted-scalar-coefficient-local-constancy` records finite local
cohomology of the restricted regular coefficient complex, including zero degrees.

`lem-sp-proetale-finite-underlying-models` records the objectwise finite set-model
consequence of local constancy and finite geometric stalks.

`lem-sp-proetale-finite-action-local-models` records the specialization of the
finite-action theorem with the localized constant-model comparison.

All four retain the item's chapter and unit and have full Lean attachments,
sources, proof steps and Mathlib searches. The first preflight caught a missing
LeanSearch category; each node now records its actual LeanSearch query and result
in addition to LeanFinder/Loogle and source grep. The complete five-file packet
compiled cleanly in the first delivery check. Some per-file axiom probes met the
busy-server response timeout; the delivery tool records these for merge rechecking. No change record is needed because
no existing statement or definition changed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
