# Completed coefficient proof transparency

## Reason

The proved private restriction and tensor-comparison helpers use local irreducibility
attributes to avoid repeated unfolding of completed-ring constructions. The command-level
preflight flags these commands for review. All existing public declaration signatures,
public imports and attributes are preserved verbatim. Two exactness proof bindings in
`purDerivedCoefficientRoundTrip` use `have` rather than `letI`, avoiding reducible instance
lets during elaboration; the data of the definition is unchanged. No source-library module
changes.

## Old

The item has no local irreducibility commands and its seven assigned theorem bodies are
`sorry`. Its `purDerivedCoefficientRoundTrip` definition uses the original two `letI`
exactness instances:

```lean
  letI := (integralDetailedCoefficientRestriction_exact W l E).1
  letI := (integralDetailedCoefficientRestriction_exact W l E).2
```

## New

The corresponding new exactness proof bindings are:

```lean
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
```

Both classes are propositions. These bindings supply the same exactness proofs to the
unchanged derived localization expression. Lean uses these local proof hypotheses as
instances. No ring, functor, comparison map or chosen object changes, and proof irrelevance
identifies the class arguments. Restoring the reducible `letI` bindings made the full-file
check exceed 60 seconds; the `have` form compiled in 44.6 seconds.

The added proof-only transparency commands are:

```lean
attribute [local irreducible] completedAdicChange
  completedIntegralCommRingSheafUnrestricted
  completedAdicChangeData integralDetailedCoefficientComparison integralCompletedScalarMap
  pbcScalarCoefficientMap purCoefficientIso

attribute [local irreducible] purRawTensorSection pbcTensorSection completedAdicChangeTensor
```

These attributes are local to this module. The fully proved private helpers expose the
identity-on-sections restriction equivalence, the adjunction comparison at the unit tensor,
and its normalized Hom equivalence. The existing seven theorem bodies are replaced by
complete Lean proofs; one uses the separate completion Roos comparison named in the report.
The existing backward elaboration and synthInstance options are retained. No compiler
limit, heartbeat, kernel-checking or generated-declaration option changes.

## Users

`Sheaf.Paper.CompletedCoefficientPresentationTransport` (M3) is the only module using
these local attributes or the new private helpers. A source search for
`purDerivedCoefficientRoundTrip` finds only this module, where `purCoefficientModel` uses
its definition with the two proof bindings above. No downstream module requires
adaptation: the public API and the mathematical data of all public definitions are
unchanged. The new public Roos
comparison and its sole consumer are documented in the new node and report.

## Status

landed 20261021T111331-L-75331 2026-10-21 (merge of deliver/M3/Sheaf.Paper.CompletedCoefficientPresentationTransport)
