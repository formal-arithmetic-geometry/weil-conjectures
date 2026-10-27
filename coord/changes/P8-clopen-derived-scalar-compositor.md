# Clopen scalar comparison proof decomposition

## Reason

The remaining comparison construction and coherence are independent portions of
the original five-step proof. They need the existing interfaces without importing
the theorem that assembles them, so the interfaces are extracted without changes.

## Old

The item contains every interface through Coherence, followed by one theorem with
one sorry. Its original theorem and all public signatures are the baseline.

## New

The item is Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor, held by P8.
The existing definitions and structures through Coherence move verbatim to the new
Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData module. The original module
publicly imports it, so all declaration names, signatures, universe parameters,
instance attributes and public import closure stay available to every consumer.
Only blueprint docstring identifiers change to attach the extracted definitions.
No target statement or mathematical definition changes. No consumer adaptation is
needed, and no source-library declaration changes.

This extraction permits new modules to state comparison descent and coherence
without an import cycle through the theorem that combines them. It is an interface
extraction, not a change intended to evade the compile limit. The original baseline
compiled in 33 seconds. The new proved unit and model modules compile separately.
The two new unfinished results are strictly separate portions of the original
argument, with all representative and naturality laws explicit.

The new public results are clopen_scalar_unit_normalization (proved),
clopen_scalar_model_properties (proved), clopen_scalar_comparison_descent, and
clopen_scalar_comparison_coherence. The main theorem assembles their conclusions
with successive_derived_quotient_normalization. There are no forced adaptations.
Independent review must check the interface extraction, new nodes, and both
remaining proof obligations; no separate worker reader was started under the
explicit dispatcher instruction.

## Users

The current library has no explicit Lean importers of the item. Its DAG parents
remain consumers of the exact theorem and interfaces when they implement their
unfinished proofs: `Sheaf.Paper.AugmentedIntegralDescent`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`, and
`Sheaf.Paper.ClopenCompletedOperationTowers`. The original public imports are retained verbatim,
and the extracted data are publicly re-exported. Every declaration name, signature
and instance attribute stays identical; the consumer requires no edit.
All other transitive importers receive the same public interface.

## Status

landed 20261024T190624-L-4164674 2026-10-24 (merge of deliver/P8/Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor)
