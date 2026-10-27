## What changed

Proved `AlgebraicGeometry.Etale.etaleSumExchangeCounit` with its original signature. The
specified sheaf base-change map is identified by iterated mates; Mathlib gives its component
and counit formulas. Exact derivation identifies the specified inverse exchange, and the
proved `exact_localization_inverse_mate` theorem yields evaluation on every unbounded object.

The fully proved constants step is in the new module
`Sheaf.AlgebraicGeometry.EtaleSumExchangeConstants`, theorem
`AlgebraicGeometry.Etale.etaleSumExchangeConstantSquare`. Three proved private helpers
`sumSquareSingle`, `sumSquareSingleMaps`, and `sumSquareSingleIsos` transport the commuting
sheaf constant square through the degree-zero embedding, using existing source coherence
lemmas. The original module retains the proved private helper `sumInverseMateComponent`.

To meet the per-file compile limit after these optimizations, the original definition
`AlgebraicGeometry.Etale.etaleSumExchangeConstantIso` is moved verbatim into
`Sheaf.AlgebraicGeometry.EtaleSumExchangeConstantIso`, which the item publicly imports.
All existing signatures, the definition body, and original public imports are preserved.
Only the item and two new Lean modules are delivered. The relocation and compatibility
checks are documented in `coord/changes/Q2-etale-sum-exchange-constants-extraction.md`.
The item's node now follows the implemented route and the constants step has its own node.

Validation: `lcompile.py --all` compiled the three delivery modules in 10.3, 28.3 and
36.1 seconds, and the unchanged direct importers `EtaleSupportExchangeRightMate` and
`EtaleSumRightAdjointCoherence` in 36.0 and 35.7 seconds. Every file passed without warnings.
The unchanged consumer test copies have been removed from the delivery.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.etaleSumExchangeCounit`
(node `lem-pur-etale-sum-exchange-counit`), proving all six conjuncts.
The new `AlgebraicGeometry.Etale.etaleSumExchangeConstantSquare`
(node `lem-pur-etale-sum-exchange-constants`) is fully proved; the extracted canonical
constant definition contains no hole. Holes closed: 1. Holes added: 0.
Unfinished split-off statements: 0. No `sorry` remains in the delivered files.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`: the specified derived adjunction
  and exactness instances are already supplied by the existing public imports.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: its separate ringed-module
  encoding is unnecessary for the existing module-valued sheaf functors.
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`: `baseChangeMap` already lives
  in the module-valued category, so its conjugation requires no additional linearity bridge.
- `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`: the proved generic
  `Sheaf.SixFunctors.ExactLocalizationInverseMate` directly identifies the derived mate.
- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison`: the proved
  `Scheme.upperStarConstantSheafIso_comp` provides the constant-composition identity directly.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: the constant definitions needed by the
  statement are provided through the public constant-comparison module.

The source single-functor and constant-composition proof imports now occur only in
`EtaleSumExchangeConstants`, where their lemmas are used. No unused import is added to the item.

Removed as proof dependencies: `lem-weil-pbc-underived-exchange-module-linear`,
`prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-sp-exact-derived-transformation-pasting`,
`lem-weil-pbc-constant-ring-inverse-image-comparison`, and
`lem-weil-pbc-constant-sheaf-maps-global-sections`. Removed the corresponding five unused
top-level `tool_uses` approvals, preserving the order of the remaining approvals.
Some remain statement dependencies or serve other consumers. Their declarations are retained.
The published derived sum adjunction still represents the needed part of
`lem-amb-etale-adjoint-locality`.

A read-only import-graph audit finds that
`Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear` leaves the targets' import
closure. The two new modules contain only proved mathematics and the unchanged construction.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was needed. The planned module-linearity bridge is
unnecessary for the specified module-valued map. The proved generic localization theorem
handles the full unbounded category, and existing constant-composition coherence replaces
the planned global-sections argument. The independent constants calculation was separated
only after optimizing it with the abstract exact-single API and profiling the concrete
alternatives. No upstream source-library declaration is changed.

## New nodes

`def-pur-etale-sum-exchange-constant-iso` owns the original canonical constant comparison,
with its unchanged construction in `EtaleSumExchangeConstantIso`. This is an extraction of
existing real data, with no new assumption or postponed proof.

`lem-pur-etale-sum-exchange-constants` is the fully proved final constants step, in
`EtaleSumExchangeConstants`; its proof is the sheaf composition calculation and exact-single
transport described above. It is strictly the sixth conjunct, independently of the mate
and counit statements. Change record:
`coord/changes/Q2-etale-sum-exchange-constants-extraction.md`.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
