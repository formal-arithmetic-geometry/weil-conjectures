## What changed

The item theorem `WeilConjectures.LisseRealization.lisse_tensor_pullback_realization` has a
complete Lean proof with its original signature. Its tensor branch combines a derived
calculation with its lisse-heart specialization. Its pullback branch constructs the integral
natural isomorphism and descends it to every raw rational morphism.

`Sheaf.CategoryTheory.ScalarLocalizationNaturalIso` proves
`CategoryTheory.ScalarLocalization.naturalIso_of_integral`: fully faithful precomposition
with the actual raw scalar localization uniquely descends integral natural isomorphisms.
It uses the existing proved categorical-localization comparison, via a private `import all`,
and Mathlib's fully faithful functor API. This removes the need to reprove scalar-fraction
naturality separately for pullback.

The unchanged five comparison-data declarations move to
`Sheaf.Paper.LisseTensorPullbackRealizationData`, publicly reexported by the item, so each
proof step can import its interface without an import cycle. The three remaining genuine
steps are separate public statements in their own modules, with source, complete proofs
in words and DAG nodes. Each is strictly a part of the original argument: derived tensor
without the lisse heart, specialization assuming that calculation, and integral pullback
naturality before rational descent.

Validation: all six delivery modules compiled using `lcompile.py --all`. The sole existing
downstream module `Sheaf.Paper.LissePointSectionsRealization` then compiled byte-identical
against the changed interfaces. Its temporary unchanged copy was removed from the packet.
The five moved declaration signatures and bodies were checked byte for byte. No data is
chosen from an unproved theorem and no definition contains a hole.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.LisseRealization.lisse_tensor_pullback_realization` (one of one).
This is a **decomposition**, not a complete mathematical proof: one upper hole closes and
three lower holes are added. The net delivery hole count is therefore -2, before any
independently proved upstream dependencies. The item's own hole count is zero.

The added holes, exactly one in each module, are:

- `WeilConjectures.LisseRealization.derived_tensor_realization`, node
  `lem-real-derived-tensor-calculation`, in `Sheaf.Paper.DerivedTensorRealization`.
- `WeilConjectures.LisseRealization.tensor_heart_specialization`, node
  `lem-real-tensor-heart-specialization`, in `Sheaf.Paper.TensorHeartSpecialization`.
- `WeilConjectures.LisseRealization.integral_pullback_normalization`, node
  `lem-real-integral-pullback-normalization`, in
  `Sheaf.Paper.IntegralLissePullbackNormalization`.

The new general theorem `CategoryTheory.ScalarLocalization.naturalIso_of_integral` is
fully proved and adds zero holes. The shared data module has zero holes. Existing imported
holes are unchanged. No claim is made that these steps have no upstream sorry dependencies.

## No longer needed

No mathematical module or node is withdrawn or globally pruned. The old dependencies
remain necessary for the corresponding split step, or for the unchanged data interfaces.
The existing unit route is preserved; the unit record has no realized step replaced here.

The following original private imports are removed from the item, whose proof now directly
uses only the four new proof modules. Their mathematical roles remain in the split-node
proof plans rather than being silently discarded:

- `Sheaf.CategoryTheory.DerivedDegreeZeroNormalization`
- `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`

The original five public imports move unchanged to the shared data module and are reexported
through it. No maintainer-approved `tool_uses` entries are deleted. In particular the
ringed-topos, completion, flat-single and degree-zero comparison nodes remain needed below
the three split statements. Zero current importers is not used as a withdrawal criterion.

## Where the brief, the DAG or earlier work was wrong

No false statement or source-library defect was found. The original plan requires substantial
model-to-derived and derived-to-heart compatibility glue; the existing declarations do not
assemble the exact universal-counit, all-good-representative and normalized-heart equations
by a single application. The packet exposes that glue as three steps with unchanged
normalizations instead of weakening the conclusion. Raw pullback naturality itself is a
categorical localization consequence and is now proved by the universal property.

New-statement edge cases were checked in the proof plans: rank zero, empty schemes, varying
finite local ranks, integral representatives with torsion cohomology, and arbitrary scheme
morphisms without base-field linearity. The heart argument uses rational local flatness,
not flatness of arbitrary integral cohomology. No global lisse lattice is assumed.

## New nodes

`def-real-tensor-pullback-comparison-data` owns the exact five moved data declarations in
`Sheaf.Paper.LisseTensorPullbackRealizationData`; it introduces no new mathematical choice.

`lem-real-derived-tensor-calculation` owns `DerivedTensorRealization` and its existence theorem.
It is the original derived tensor calculation and unit normalization, excluding every heart
specialization claim.

`lem-real-tensor-heart-specialization` assumes that derived calculation and proves its
coherent lisse-heart comparison, representative normalization and degree-zero equation.

`lem-real-integral-pullback-normalization` constructs the actual normalized integral
pullback square and proves naturality on integral arrows. The item supplies rational descent.

`lem-real-raw-localization-natural-iso` records the fully proved unique rational descent theorem.
It uses categorical localization, without target linearity or additivity assumptions.

Change record: `coord/changes/lisse-tensor-pullback-shared-data.md`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
