## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.boundary_duality_input` by a
formal assembly of normalized geometric comparison data. The public signature,
coefficient level n+1, canonical operations, and both boundary conclusions stay
unchanged. No source-library module, target, or existing definition is changed.

The new module `Sheaf.SixFunctors.BoundaryNormalizedModels` defines a concrete
structure of geometric inputs before the boundary transpose argument and states
one sourced geometric realization lemma. There is no sorry in a definition and
no arbitrary data is extracted into a public definition from that lemma.

The item now explicitly identifies its delta, alpha and boundary exchange with
the native internal-Hom arrows, applies the proved `bidual_transpose`, derives
exchange invertibility from three invertible factors, and derives the exact
requested double-dual compatibility. A private lemma proves opposite currying directly from tau naturality at (id,delta),
evaluation of delta and cancellation of symmetry. Another proves isomorphism
invariance of the actual finite-Tor constructible predicate by transporting
constructibility and each Tor-interval representative.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.ProEtale.boundary_duality_input` (node
`cor-weil-boundary-duality-discharge`). The item has zero remaining sorries.

Added exactly one sorry, the public theorem
`AlgebraicGeometry.ProEtale.BoundaryDualityInput.boundary_normalized_models`
(node `lem-weil-boundary-normalized-models`). This is a decomposition: one upper
hole closed and one geometric hole added, net zero holes closed. It does not
claim a completed proof without sorry dependencies. The open theorem assumes neither isomorphism closure nor the opposite-currying
equation; the delivered proof establishes them. It does not
assert invertibility of beta or its double-dual compatibility; those conclusions
are proved by the delivered Lean calculation.

The private helpers `model_delta`, `model_exchange`, `model_alpha`,
`formal_opposite_currying`, `assertions_of_normalized_model` and `ctf_closed_under_iso` are complete proofs.
Existing imported theorems may still depend on their own named sorries; none is
replaced or counted as closed here.

## No longer needed

All original proof-only imports below are removed from the item, which instead
imports the new normalized-model module. This is import cleanup, not withdrawal
of their declarations or a claim that all their mathematical content is obsolete.
Several remain transitive imports or ingredients of the geometric lemma's proof
plan. In particular the finite-Tor domain and finite-site realization steps remain
needed there. No Lean module is withdrawn, and no DAG node is deleted.

- `Sheaf.Paper.FiniteStageVerdierBiduality`
- `Sheaf.Paper.PullbackTorAmplitude`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.SixFunctors.ClosedCostalkDuality`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.Paper.DualityPairing`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.Paper.ProjectionCompactification`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.BoundaryDualizingComposition`
- `Sheaf.Paper.BoundaryProEtaleProjectionComparison`
- `Sheaf.Paper.BoundaryProEtaleQCompatibility`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.SixFunctors.BoundaryAlphaNormalization`
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`

The original parent proof dependency list is replaced by the model lemma,
`lem-weil-boundary-bidual-transpose`, and the input definition. Geometric
dependencies are recorded on the model lemma, where they are needed. This does
not bypass the unit's boundary-duality statement or remove a source-library
statement. No whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original fourteen-step docstring was out of date with the four-step DAG.
The declared geometric lemmas use different coordinate packages from the literal
`CanonicalOperations` and `Assertions` required here. In particular an
existence-only costalk isomorphism does not normalize alpha, and the etale
finite-Tor preservation statement does not by itself construct all fixed
pro-etale coordinate fields. The new lemma records that remaining interface
construction explicitly, retaining the specified theta and tau equations and
alpha normalization. The formal bidual-transpose argument is genuinely separate
and is now checked in Lean rather than left in prose. The unused target-side
subcategory in bidual_transpose is instantiated with the top predicate, so
exceptional preservation is not an assumption of the new model.

Edge cases: the coefficient level is positive for n=0 as well as n>0; pieces and
boundaries may be empty; the formal argument uses no nonemptiness, cancellation
of a zero object, or geometric-point assumption. Naturality is required only on
finite-Tor inputs; tau retains the arbitrary second input required by the
original Assertions interface. The model uses the actual canonical functors and
native evaluation, not a substitute duality. No target signature is weakened.

An optional direct construction of the canonical-operation record encountered
expensive kernel conversion through the derived localization structures. It is
kept only as a scratchpad text file and is not part of the delivery. The two
actual delivered modules compile through the required compilation tool.

## New nodes

`def-weil-boundary-normalized-model` records the concrete input structure in
`Sheaf.SixFunctors.BoundaryNormalizedModels`. It contains dual preservation, pullback preservation, native biduality,
normalized maps, naturality and alpha-isomorphism information needed before
formal transposition; all data are explicit fields, with no hollow definition.

`lem-weil-boundary-normalized-models` is the sole remaining geometric theorem.
Its docstring and DAG node give the finite-Tor domain, evaluation normalization,
projection-formula and comparison transport argument, with the existing node
references. Its conclusion excludes both final beta assertions. The original
node's proof and proof dependencies are updated to match the Lean assembly.
There are no statement-change records because no existing public statement or
definition is changed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
