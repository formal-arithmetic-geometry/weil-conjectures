## What changed

The original `AlgebraicGeometry.ProEtale.constructibleComparison` now has a complete Lean proof
combining locality, classicality, the module equivalence and bounded derived restriction.
Its signature is unchanged. The three existing canonical constructions move verbatim to
`ConstructibleProEtaleComparisonData`, publicly imported by the original module, to allow
lower proof modules to use them without an import cycle. No arbitrary functor or object is
chosen from an admitted existence theorem to define the canonical data.

The local equivalence is proved by affine refinement, finite subcovers and the existing
stratification gluing theorem. The qcqs classicality clause is proved from continuity for
one global stratification. The constructible module equivalence is constructed by a lifted
fully faithful functor and classical descent. Exactness of the actual module inverse image
is proved by constant-ring presentation and the underlying additive-sheaf comparison;
Mathlib then supplies its derived localization, cohomology compatibility and compatibility
with modules in degree zero. The bounded equivalence is constructed explicitly by preserving
and reflecting constructibility and the same finite cohomological interval.

Module full faithfulness and classical descent are derived from bounded classical comparison
using the degree-zero embedding, rather than left as another admitted conjunction. Its
irreducible degree-zero construction has proved APIs for full faithfulness, cohomology and
bounds, avoiding repeated unfolding of large zero-object instances.

Validation: every delivered Lean module is compiled singly in sandbox import order by
`lcompile.py --all`; the original four signatures and the three moved bodies are compared
verbatim after whitespace normalization. The DAG dependency graph is checked for missing
nodes and cycles. The unchanged `ConstructibleComparisonModuleExact` and
`ConstructibleComparisonFlatPullback` consumers both compile against the sandbox
(14.2 s and 10.6 s respectively); neither is included as an adaptation. No module under
`WeilConjectures` is modified. A refreshed server preflight found a third user,
`ConstructibleComparisonTensorTestReflection`, landed during the session. It also compiles
unchanged against the sandbox (16.8 s), and is included in the change record's user table.

## Proved and sorry left

This is a decomposition with substantial proved glue, not an axiom-free proof of the target.
One original hole is closed: `AlgebraicGeometry.ProEtale.constructibleComparison`.
Three source-backed holes are added (net minus two holes before import-closure pruning):

- `AlgebraicGeometry.ProEtale.coefficientStratified_continuity`, node
  `lem-pe-coefficient-stratified-continuity`: continuity for one global finite stratification.
- `AlgebraicGeometry.ProEtale.coefficientComparison_constructibilityTest`, node
  `lem-pe-coefficient-comparison-constructibility-test`: preserve and reflect the stratum
  property for a given etale module; no equivalence or antecedent assertion.
- `AlgebraicGeometry.ProEtale.coefficientComparison_boundedClassical`, node
  `lem-pe-coefficient-bounded-classical-descent`: bounded morphism bijections and classical
  descent, without constructibility, Noetherianity or qcqs assumptions.

These are all remaining `sorry`s in the delivery. Each is a public theorem with proof exactly
`:= by sorry`, a source, a complete proof in words, its own module and a matching DAG node.
The local clause and the ambient exact derived-functor construction introduce no new holes.
The full original theorem still depends on these three holes, so zero original sorries are
fully discharged without the new admissions.

Proved public helpers: `constructibleComparison_local`, `constructibleComparison_classical`,
`constructibleComparison_moduleEquivalence`, `constructibleComparison_derivedFunctor`,
`constructibleComparison_boundedRestriction`, `coefficientComparison_moduleCriteria`,
`coefficientProEtale_constructible_of_iso`, `coefficientProEtale_finite_iso`,
`coefficientProEtale_finite_comp`, `coefficientSingle_bounded`, `coefficientSingle_classical`,
`coefficientSingle_full_faithful`, `coefficientSingle_homologyIso`, and the full/faithful
instances for `coefficientModelSingle`. The data definitions contain no admissions.

## No longer needed

Removed the original private imports of `ProEtaleClassicalSheavesModules`,
`ConstructibleProEtaleClassical`, `ProEtaleFiniteLocalSystemsTwist`,
`BoundedBelowProEtaleComparison`, `ProEtaleDirectImageComparison`,
`WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`,
`ClassicalDerivedEquivalence`, and `CoefficientConstructibleEtaleModules` from the item module.
The gluing theorem is imported by the lower locality and classicality proofs. The finite-system,
classical-sheaf, direct-image and bounded-classical results remain mathematical dependencies
of the three remaining coefficient-sized source lemmas; they are not declared globally obsolete.
The specialized `det-pe-constructible-comparison-classical` declaration itself is not applied.

The dedicated affine-opens-basis step is replaced by Mathlib's
`exists_isAffineOpen_mem_and_subset`, used directly. No source declaration or module is
withdrawn. The unit's locality → classicality → module equivalence → bounded restriction
route is retained; its old proof dependencies are represented through the corresponding
new lower node records. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing declared classical comparison and finite-local-system interfaces couple the
coefficient universe to the scheme universe (`Type (u+1)` or `ULift` of `Type u`), while this
item retains the independent coefficient size `max v (u+1)`. They cannot simply be applied
to the displayed canonical intrinsic functor. The three remaining results explicitly record
the coefficient-sized comparison arguments still needed; their docstrings explain the
constant-scalar and site equivalences and the geometric source arguments to generalize.
This is an interface gap, not a disputed mathematical assertion or an unsupported dependency.

An existing proved exactness helper imports the original item publicly, so importing it back
would form a cycle. Its proved constant-ring presentation argument is reused as private
helpers below the new data module, with attribution, retaining the original source module.

Small cases checked in the mathematical statements: empty scheme and partition, zero module
and complex, zero ring, nonreduced strata, coefficients with torsion, and a finite nonprojective
module over a Noetherian ring. No finite coefficient-set or local freeness hypothesis is added.

## New nodes

`lem-pe-coefficient-bounded-classical-descent`: Bounded classical derived comparison on coefficient-sized sites. Lean module `Sheaf.AlgebraicGeometry.CoefficientBoundedClassicalDescent`.

`lem-pe-coefficient-bounded-constructible-restriction`: Reflection of bounds and restriction to constructible complexes. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence`.

`lem-pe-coefficient-classical-single`: Degree-zero modules, bounds, and continuity. Lean module `Sheaf.AlgebraicGeometry.CoefficientClassicalSingle`.

`lem-pe-coefficient-comparison-constructibility-test`: The stratum property test for canonical inverse image. Lean module `Sheaf.AlgebraicGeometry.CoefficientComparisonConstructibilityTest`.

`lem-pe-coefficient-comparison-data`: Canonical coefficient-sized comparison constructions. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`.

`lem-pe-coefficient-comparison-derived-functor`: Exact canonical comparison descends to the standard derived categories. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor`.

`lem-pe-coefficient-comparison-module-criteria`: Module comparison from degree-zero derived comparison. Lean module `Sheaf.AlgebraicGeometry.CoefficientComparisonModuleCriteria`.

`lem-pe-coefficient-constructible-classical`: Finite-cover passage from affine constructibility to continuity. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical`.

`lem-pe-coefficient-constructible-iso`: Constructibility is invariant under intrinsic module isomorphism. Lean module `Sheaf.AlgebraicGeometry.CoefficientProEtaleConstructibleIso`.

`lem-pe-coefficient-constructible-locality`: Affine and pointwise constructibility agree. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal`.

`lem-pe-coefficient-constructible-module-equivalence`: Restriction to constructible module sheaves. Lean module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence`.

`lem-pe-coefficient-finite-local-model-pullback`: Finite module local models survive iterated inverse image. Lean module `Sheaf.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback`.

`lem-pe-coefficient-stratified-continuity`: Continuity from a single finite stratification. Lean module `Sheaf.AlgebraicGeometry.CoefficientStratifiedContinuity`.

Change record: `coord/changes/constructible-comparison-constructions.md`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
