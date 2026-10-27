## What changed

Filled seven existing theorem proofs in `Sheaf.Paper.CompletedModelSectionsTransport`,
without changing any signature or definition. Additivity uses the recorded additive
change-of-rings witness and additive constant sheafification. The cochain calculation
checks the generator `1 tensor x` using the actual unit characterizations and the
sections-tensor formula. Derived naturality cancels the specified completion isomorphism,
then applies naturality of theta and the model units; rational naturality uses beta.
The finite-subfield conclusion specializes `transport_eq` after converting both intrinsic
constructibility hypotheses. The three raw-localization clauses use the semilinear
extension API, with Mathlib module-localization surjectivity providing one denominator.
Representative independence follows by applying the actual extension functor to an
equality of fractions. Coherence localizes the given integral square, and the
contravariant clause applies the same result to the opposite category.

## Proved and sorry left

Closed seven of the twelve original holes (namespace
`WeilConjectures.CompletedModelSections`):

- `realization_additive`
- `chainTransport_spec`
- `transport_naturality`
- `completedModelSectionsTransport`
- `scalarLocalizedNaturality`
- `scalarLocalizedCoherence`
- `scalarLocalizedContravariant`

Five existing holes remain, all attached to
`lem-pod-completed-model-sections-transport`:

- `unit_existsUnique`
- `derivedMap_existsUnique`
- `transport_eq`
- `transport_identity`
- `transport_tower`

No new holes, split-off statements, axioms, or data definitions were added. These
proofs use the existing named obligations as intended by stage 3; this is a partial
proof delivery, not a claim that the full node has become axiom-free.

## No longer needed

Removed unused private proof imports of:

- `Sheaf.Paper.PointFiniteFreeSectionsTensor`
- `Sheaf.Paper.PointDerivedSectionsTensorDescent`
- `Sheaf.Paper.PointDerivedTensorTowerCoherence`
- `Sheaf.Paper.CoefficientComplexRationalization`
- `Mathlib.Algebra.Homology.DerivedCategory.KProjective`

The implemented proofs use the public comparison API of
`Sheaf.Paper.PointSectionsScalarExtension`. No module or node is withdrawn: the five
remaining obligations retain their original sources and proof plans, so their planned
dependencies remain needed. Added the private proof import
`Mathlib.RingTheory.Localization.BaseChange` for localized-module surjectivity.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The initial error-heavy compile exceeded 60 seconds; local
irreducibility controls on the completed model definitions keep elaboration controlled
without altering any published definition. The final profiling compile passed in
30.8 seconds; profiling options were removed for delivery.
The common-denominator argument can use
`IsLocalization.tensorProduct_isLocalizedModule` and `IsLocalizedModule.surj`
directly, including torsion and the zero localization. Independence of fraction
representatives follows from the extension functor's already proved fraction formula.
The cochain equality only needs generators `1 tensor x`, since the compared maps are
linear. Naturality uses the theta natural isomorphism directly after completion
cancellation; representative independence remains in `derivedMap_existsUnique`.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
