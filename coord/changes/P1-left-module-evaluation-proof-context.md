# CategoryTheory.leftModuleDerivedEvaluationForget: local proof context

## Reason

The completed proof adds private helpers, their section variables and opens,
local composition-preservation instances, and elaboration options. Preflight
classifies the difference in top-level commands conservatively as an interface
change and requires this record. Every pre-existing declaration has its original
signature and visibility; every pre-existing definition and instance body is
unchanged. The four public imports remain identical. All added declarations are
private. There is no exported notation, instance, attribute, or definition change.

## Old

The original file's elaboration settings and global context were:

```lean
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
```

The original final `namespace CategoryTheory` contained only the main theorem.

## New

The corresponding context is:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The private-helper namespace additionally opens
`ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation`, installs the same
local instances, and introduces section variables for its private proofs. The
private injective-acyclicity helper opens `ConstantLeftModuleInverseImage`.
The main theorem's namespace opens both namespaces. All these commands are
local elaboration context; imports do not inherit these options or opens, and
`[local instance]` does not register an exported instance. Public types and
mathematical meanings therefore agree verbatim. No target definition or
statement changes, so no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
--direct` lists the following direct importers (all remain unedited). The
transitive downstream census is 1076 modules. The declaration-use check has no
changed public declaration to match. Every direct importer receives the same
public interface; this also applies to its transitive importers. No consumer
adaptation or change of ownership is involved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed; not adapted | None; local context only. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity | unclaimed; not adapted | None; local context only. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed; not adapted | None; local context only. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed; not adapted | None; local context only. |
| Sheaf.CategoryTheory.ModuleRestrictionKernelComparison | unclaimed; not adapted | None; local context only. |
| Sheaf.Paper.NearbyClosedImage | unclaimed; not adapted | None; local context only. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed; not adapted | None; local context only. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed; not adapted | None; local context only. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed; not adapted | None; local context only. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed; not adapted | None; local context only. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed; not adapted | None; local context only. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed; not adapted | None; local context only. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed; not adapted | None; local context only. |
| Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity | unclaimed; not adapted | None; local context only. |

The item compiled through `lcompile.py` without errors or warnings in 24.3 s.
The independent reader can inspect the local command classification and the
unchanged public declarations without consumer proof adaptations.

## Status

landed 20261019T005353-L-2759610 2026-10-19 (merge of deliver/P1/Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget)
