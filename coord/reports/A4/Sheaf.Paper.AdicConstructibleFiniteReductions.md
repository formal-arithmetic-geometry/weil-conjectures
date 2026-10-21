## What changed

Proved `AlgebraicGeometry.Scheme.adicFiniteOrdinaryComparison_existsUnique` with its
original statement. The argument works for any commutative coefficient square:
construct the induced module direct image for the target coefficient ring and
restrict its scalars along the source coefficient map. Both routes are left
adjoint to this same functor. Uniqueness of left adjoints gives the comparison,
and the normalized Hom equivalences give precisely the required insertion
formula. Scalar associativity supplies the other side of the square. Applying
the Hom equivalence again proves uniqueness of every component. Naturality of
the constant-ring comparison specializes the argument to the specified small
etale/pro-etale comparison.

Reused the already proved private scalar adjunction from
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, removing its duplicate
local construction and retaining a proved API for evaluation on pure tensors.
This addresses the full-file compile timeout encountered when adding the new
proof. The change record describes the private-helper adaptations. Public
statements, definitions, public imports and coefficient universes are preserved.
The existing private derived comparison now gives its two natural transformations
by explicit component maps and uses a single associativity equation for their
normalization. Its two isomorphisms on complexes are likewise specified by
components. The naturality proofs are those of the original composites. In the derived-unit
proof, only preservation of quasi-isomorphisms is transported across the ordinary
functor equality; the surrounding construction is not globally substituted.

Updated the item's node proof, proof dependencies and proof origin to record the
ordinary comparison argument and its existing induced-modules and module-adjunction
dependencies. No new node or independent result is split off. The private-definition reuse is
recorded in `coord/changes/A4-adic-finite-ordinary-comparison.md`.

The general coefficient-square proof was independently compiled in a scratch
module. `#print axioms` there reports only `propext`, `Classical.choice` and
`Quot.sound`. The full module compiled in 56.8 seconds under the existing 60-second
limit. The new ring-data constructor is explicitly `noncomputable`: its isolated
profile confirms that this omits unnecessary executable-code generation and
keeps its mathematical data unchanged. Both added dependency imports pass
`import_direction.py may`.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Scheme.adicFiniteOrdinaryComparison_existsUnique`.

The sole remaining `sorry` is the original named theorem
`AlgebraicGeometry.Scheme.adic_constructible_finite_reductions`. Its signature,
source, complete ten-step natural-language proof, and DAG attachment
`lem-sfb-adic-constructible-finite-reductions` are retained.
Its remaining work is the completeness/derived-limit comparison, the nilpotent
reduction Tor and constructibility arguments, and the descent with the prescribed
quotient cocycle. No new `sorry` is added. This packet is a proof of one hole,
not a decomposition of the other.

## No longer needed

No node or module is withdrawn. The remaining finite-reductions theorem still
needs its original declared dependencies; they are not pruned merely because its
proof is unfinished. The new ordinary comparison uses an existing normalized
adjunction instead of rebuilding scalar extension section by section.

The duplicate private helpers removed from this module are
`adicFiniteOrdinaryUnitApp`, `adicFiniteOrdinaryUnitApp_apply`,
`adicFiniteTensorToRestriction`, `adicFiniteRestrictionToTensor`,
`adicFinitePresheafHomEquiv`, `adicFiniteHomEquiv_naturality_left`, and
`adicFiniteHomEquiv_naturality_right`. Their required content is supplied by the
existing scalar adjunction and the retained proved section-evaluation API.
No public declaration or adopted source-library declaration is removed. Two proof
imports are added and the completed-pullback proof import is changed to `import all`
to access its proved normalization helper.

The following proof imports are unused by the current proofs and are removed.
The corresponding planned dependencies of the still-unproved main theorem remain
in the DAG; removing a proof import does not withdraw a planned result.

- `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsExact`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Paper.NilpotentReductionLissity`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.Paper.LocalizeRingedSiteMorphism`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Paper.LocallyConstantTensor`
- `Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical definition defect was found. The ordinary
comparison can be proved through normalized adjunctions, without constructing a
second tensor coequalizer inverse by hand. The node now records that route.

The first combined full-file attempt exceeded the existing 60-second limit.
Profiling and separate definitional-equality checks identified the duplicate
local scalar-adjunction construction. Reusing the existing proved construction,
giving the derived comparison maps explicit component equations, and replacing
normalization simplification by associativity avoid unnecessary reductions.
A further delay came from executable compilation of the new ring-data constructor,
which waited for preceding proof checks. An explicit `noncomputable` modifier
avoids generating executable code for this purely mathematical construction.
The limit was not changed and no delivery module was split for performance.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
