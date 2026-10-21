## What changed

Restored the assigned quarantined module from the current rework record, preserving every
existing declaration, signature, definition, public import and Lean attachment. Replaced
two of its six theorem holes with complete Lean proofs. Open normalization follows the
iterated-mate identity and the already proved normalized scalar/pullback identification;
naturality follows the two constituent naturality squares and functoriality. Added the
proof-only `import all Sheaf.Paper.EtaleProEtaleScalarMate` to reuse its proved private
`scalarPullback_eq`, without introducing another public comparison. Updated the existing
node's open-normalization step and proof dependencies to record that shorter route.

The restored module compiles through lcompile.py, including after removal of unused proof
imports. The import-direction check permits the new dependency. No other module, target,
statement, definition, universe, or public interface was changed.

## Proved and sorry left

Closed 2 of the 6 original holes, with no new holes and no split-off statements:

- `AlgebraicGeometry.Etale.compactScalarOpen_normalization`.
- `AlgebraicGeometry.Etale.compactScalarMap_naturality`.

The following four original theorem holes remain, all attached to
`lem-pur-etale-compact-scalar-coherence`, with their existing source and complete proof
plans preserved:

- `AlgebraicGeometry.Etale.etaleCompactScalarCoherence`.
- `AlgebraicGeometry.Etale.etaleCompactScalarComposition`.
- `AlgebraicGeometry.Etale.etaleCompactScalarOpenRestriction`.
- `AlgebraicGeometry.Etale.etaleCompactScalarUnit`.

This is a partial proof delivery, not a decomposition or a claim that the full node is
proved. In particular, the remaining four proofs have not been replaced by equivalent
new holes. The reused inverse-mate identification is already proved in its own module;
its existing dependencies remain work for their own items.

## No longer needed

The two completed proofs need no new K-flat calculation for open extension: the normalized
inverse-mate identification and adjunction equations suffice. Removed these unused
proof-only imports from the restored module:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.Topology.Defs.Filter`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.ProperOpenCoefficientMate`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.

No declaration or module is withdrawn, and no complete DAG node is claimed globally
unnecessary: the four remaining coherence proofs retain their original plans and their
needed dependencies. In particular, the K-flat, tensor, composition, refinement and
exchange results may still be needed for those remaining proofs. All eight public imports
are preserved. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined rather than present under lean/. Its current rework archive is
the baseline restored here; its absence is not treated as withdrawal. The original
open-normalization plan is valid but longer than necessary given the existing proved
inverse-mate identification. No statement dispute or tool failure was found.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
