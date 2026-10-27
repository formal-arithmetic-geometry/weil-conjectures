## What changed

Reduced `WeilConjectures.OpenFactorCoherence.openFactorCoherence` to three
strictly smaller realization statements, retaining all four declared dependencies
of its existing DAG plan. The theorem assembles its original `Assertion` without
changing any hypothesis, universe, field or conclusion.

The four private proved helpers establish the actual `gamma_unit` and `beta_unit`
equations by completion-unit naturality, and `gamma_iso` and `beta_iso` by
composition of isomorphisms. The final uniqueness proof uses injectivity of
precomposition with the actual horizontal completion unit.

Extracted `Open`, `gamma`, `theta`, `OrdinaryExchange` and `beta` verbatim to
`Sheaf.SixFunctors.OpenFactorCoherenceData`, publicly re-exported by the item.
This permits realization modules to state their conclusions without an import
cycle through the theorem being proved. Every original public import remains.
See `coord/changes/Y8-open-factor-fixed-data-extraction.md`.

## Proved and sorry left

Closed the original hole of
`WeilConjectures.OpenFactorCoherence.openFactorCoherence`
(node `lem-sf-pf-open-factor-coherence`) by a complete assembly proof.
This is a decomposition, not a net proof of the whole mathematical result:
one upper hole closed and three lower holes added.

Proved private helpers: `gamma_unit_formal`, `gamma_isIso_formal`,
`beta_unit_formal`, `beta_isIso_formal`, and `fixedOpen_exists`.

Exactly three holes remain in the delivery, all named public theorems in separate
new modules, with full source-based proofs in words and matching nodes:

- `WeilConjectures.OpenFactorCoherence.openFactorOpenRealization`,
  `lem-sf-open-factor-open-realization`: fixed coefficient realization of the
  open extension/restriction, reduction and completeness data only.
- `WeilConjectures.OpenFactorCoherence.openFactorProjectionRealization`,
  `lem-sf-open-factor-projection-realization`: fixed tensor/restriction comparison
  and its unit and restricted-projection equations only.
- `WeilConjectures.OpenFactorCoherence.openFactorExchangeRealization`,
  `lem-sf-open-factor-exchange-realization`: fixed horizontal pullback and exchange
  normalization, restricted unit square and precomposition injectivity only.

No remaining hole is inside a definition, a private helper, or the assembly.
No arbitrary operation is chosen from a mere existence theorem: the assembly only
eliminates existential data inside its `Nonempty Assertion` proof.

## No longer needed

No declared proof dependency is pruned: all four planned lemmas are used.
No module is withdrawn. Every original public import is preserved. Removed
private proof imports (fully qualified, to make the pruning explicit):

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`
- `Mathlib.RingTheory.Ideal.Operations`
- `Mathlib.RingTheory.Ideal.Quotient.Defs`
- `Mathlib.RingTheory.LocalRing.Basic`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Mathlib.Topology.Compactness.Compact`
- `Mathlib.Topology.NoetherianSpace`
- `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`

These modules are not claimed to be globally unnecessary: their mathematics is
still used by the four planned results and the three realization steps. The
final assembly imports only the three realization modules as proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The four-step DAG assembly is mathematically appropriate, but its published Lean
conclusions are not the same presentation as this module's `Assertion`.
OpenRoos uses normalized slice `Operations` and the unrestricted completeness
predicate; OpenTensorQuotient supplies the normalized tensor models and finite
geometry in that slice presentation; OpenProjectionRoos restricts its main map
to constructible pairs; OpenExchangeRoos uses `pbcIntegralDatum` and its fixed
coefficient transport, and states its square on complete inputs. The missing
work is the explicit fixed-presentation comparison, including the ambient square
and tensor/restriction data. The new statements isolate those genuine steps;
they do not rename the full theorem. Gamma and beta invertibility and unit
equations are formal once the data exist, so they need no new holes.

Checked empty and identity opens, zero complexes and tensor inputs, the first
positive quotient, identity horizontal arrows and empty cohomological intervals.
The open interval clause deliberately does not assume a ≤ b: exact degreewise
cohomology handles that case as well.

## New nodes

`def-sf-open-factor-fixed-data` owns only the existing declarations extracted
verbatim to `OpenFactorCoherenceData`; it adds no mathematical assumption.

`lem-sf-open-factor-open-realization` realizes clauses (1) and (2) and the strict
extension/completion comparisons from the declared open and quotient lemmas.

`lem-sf-open-factor-projection-realization` realizes only the completed tensor
comparison and its restriction/unit equations from the existing Roos projection.

`lem-sf-open-factor-exchange-realization` realizes only the horizontal pullback
and exchange data and the unit-precomposition injectivity used for uniqueness.

The existing node now records the actual four-step Lean assembly. The unit's
statement and route are unchanged. Change record:
`coord/changes/Y8-open-factor-fixed-data-extraction.md`.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
