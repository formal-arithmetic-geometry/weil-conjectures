# CommonStageCalculus private proof context

## Reason

Complete the eight remaining proofs using generic tensor-Hom shift constructors,
localization descent, adjunction mates, and common-stage finite products. Private proved
helpers keep the concrete coefficient construction out of generic elaboration. The
transparency settings distinguish the abstract tensor calculations from the existing
quotient calculations; they affect elaboration only. The local irreducibility attribute
is on a new private proof helper. The final two settings restore transparency-respecting
elaboration after the quotient calculations. The integral and rational associator proofs
specialize generic coherence helpers. The pointwise normalization is converted to a
natural-transformation equation before specializing the coefficient categories.
The two scoped unused-variable settings preserve the
existing instance-binder names in the two existence theorems.

Every existing signature, visibility, public import, instance attribute and non-theorem
body stays unchanged. No definition or target statement changes its meaning. No source
library file is edited. All new helpers are private and proved. Returned duplicates of `exactUnitLocus`,
`uniformProfileLocus`, `pbcKanCommShift_ext` and `pbcScalarLocalization_isLocalization`
are removed; their existing private declarations are used through proof-only
`import all` commands. Their owning modules and visibility remain unchanged.

## Old

The existing settings were:

```lean
set_option autoImplicit false
set_option linter.unusedSectionVars false
```

No existing declaration signature or definition body is replaced.

## New

The settings and new local attribute in source order are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorShiftCore
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The existing public shift instances still choose precisely the unique structures
specified by their original existence theorems. The generic construction and uniqueness
proof fill those theorem proofs; they do not change the instance definitions.

## Users

The direct consumer scan was
`python3 tools/downstream.py Sheaf.Paper.CommonStageCalculus --direct --names`.
All consumers retain the same public declarations, definition bodies, public imports,
and instance attributes. No consumer adaptation is necessary. Indirect consumers
therefore also retain the same interface and meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | A9 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | Unchanged public interface; no adaptation. |

## Status

landed 20261021T110942-L-3837323 2026-10-21 (merge of deliver/B8/Sheaf.Paper.CommonStageCalculus)
