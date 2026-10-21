## What changed

Proved `AlgebraicGeometry.Scheme.coefficientProEtale_tor_interval_triangle` with its
statement and definitions unchanged. Resolve each test sheaf in degree zero, use the
published K-flat tensor's coherent shifts, and transport triangulatedness through its
localized augmentation. Apply Mathlib's `DerivedCategory.HomologySequence.exact₂`.
The proved representative and tensor-test comparison lemmas from
`Sheaf.AlgebraicGeometry.CoefficientTorFlatModel`, together with the fixed-tensor
resolving comparison, identify the actual coefficient-model Tor predicate with the
vanishing used in that exact sequence. The minimum/maximum bound and its common
interval specialization then follow by exactness and integer inequalities.

Removed the redundant direct private import of
`KFlatResolutionIndependentCoefficients`: the proved representative theorem already
encapsulates that construction. Added private proof imports of `CoefficientTorFlatModel` and
`TensorColimitsIndependentCoefficients`; the latter supplies the existing comparison
between monoidal and sectionwise sheaf tensor flatness. Updated the item's DAG proof,
proof dependencies and proof origin to describe these precise comparisons. No public
interface, target, source-library file, definition, or consumer is changed.

Validation: the final module compiled cleanly through `lcompile.py` in 10.9 seconds,
with no warnings. A textual comparison checked that the theorem signature, both
existing definition/instance bodies, all docstrings, and all public imports are
unchanged. Every line is at most 100 characters.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.coefficientProEtale_tor_interval_triangle`
(node `lem-weil-proetale-tor-interval-triangle`). Added zero holes; zero textual
`sorry` remain in the delivered Lean module. This is a proof from existing stated
dependencies, including `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`,
whose existing proof hole remains in its own unchanged module. No new lemma is split off.

## No longer needed

Removed the private import `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
now encapsulated by the existing proved flat K-flat representative theorem.
Removed the private import `Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`
and the direct proof dependency/tool-use entry
`lem-weil-derived-tensor-resolution-independent`. Its geometric-site statement is
unnecessary: the fixed-tensor theorem already gives the natural resolving comparison
for arbitrary second complexes, and the proved coefficient-model tensor-test comparison
covers every K-flat representative. This is pruning from this item's route only; no
module is withdrawn, and no claim is made that other consumers no longer need it.

The proof does not use the declaration currently attached to
`def-weil-derived-tensor` (the fixed-ring pro-etale presentation). Its direct proof
edge is removed; the statement dependency remains unchanged. The actual published
derived tensor used by this module is the existing coefficient-site descent bifunctor.
The direct proof edge to `lem-pc-kflat-resolution` is likewise redundant: it is
encapsulated by the proved flat K-flat representative theorem. The other planned
cohomology and Tor-predicate dependencies are retained. The additional coefficient-model lemmas
are generic representative comparisons; the unit's ambient typing route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned direct use of `derivedTensor_resolution_independent` has a different site
and universe presentation from the item's coefficient-sized small site. No interface
repair is needed: the already stated fixed-tensor theorem provides the needed natural
comparison directly. The original plan also described the Tor predicate as vanishing
of the published derived tensor, whereas the actual predicate quantifies over every
K-flat representative. The proof explicitly bridges these using the existing proved
`exists_coefficientModelFlatKFlatRepresentative` and `coefficientModelTensorTest_iso`.
These comparisons retain all test sheaves and require no constructibility, finiteness,
or flatness of the test sheaf. The zero sheaf, zero ring, equal or disjoint outside
intervals, negative endpoints and non-flat test sheaves are covered by the same argument.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
