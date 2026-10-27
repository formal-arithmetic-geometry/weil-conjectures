## What changed

Filled `WeilConjectures.systemScalarOrdinaryAdjunction_existsUnique` in
`Sheaf.Paper.CompactSupportSystemTransposeNormalization`. The proof applies the
existing section-normalized sheaf-ring adjunction to the fixed scalar model and
its object/map identifications. The section formula for the unit follows by
transport across the inverse object equality. For uniqueness, the same section
formula identifies the units after an injective equality transport; units then
determine adjunction structures.

The fixed scalar model is locally marked irreducible during the scalar section;
the chosen scalar adjunctions, fixed model and derived functor are locally kept
folded during the final section. These prevent expensive elaboration of chosen
constructions. No exported statement,
definition or attribute changes. All other existing theorem bodies remain as
received.

## Proved and sorry left

Closed one of the original seven holes:

- `WeilConjectures.systemScalarOrdinaryAdjunction_existsUnique`.

Added no holes and no split-off statements. Six existing holes remain unchanged,
all attached to `lem-weil-compact-support-system-transpose-normalization`:

- `WeilConjectures.systemScalarAdjunction_existsUnique`.
- `WeilConjectures.wholeMixedReductionUnit_existsUnique`.
- `WeilConjectures.realizedSystemPush_existsUnique`.
- `WeilConjectures.realizedSystemPullInv_isIso`.
- `WeilConjectures.realizedSystemRestriction_existsUnique`.
- `WeilConjectures.compactSupportSystemTransposeNormalization`.

This is a partial proof delivery. Attempts at the derived adjunction and ordinary
pushforward comparison are not included because that larger candidate has not
passed the fixed compilation limit. No completion of the final normalization is
claimed.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.Algebra.Homology.CochainDerivedAdjunction`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Paper.QuotientScalarComparisonDescent`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor`.
- `Sheaf.CategoryTheory.AugmentedScalarRoosResolution`.

No node or module is withdrawn. The unproved parts retain the existing DAG proof
plan and dependencies, including the cochain, mixed-unit and Roos arguments.
Removing a direct import unused by this partial proof does not establish that
those mathematical dependencies can be pruned from the remaining argument.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing ordinary adjunction theorem suffices
for the first helper hole, including its uniqueness; no new intermediate theory
is needed. No faithfulness of separate derived evaluations is used.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
