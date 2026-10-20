# DerivedCategory.reconstruction_models: proof elaboration commands

## Reason

The proof adds private helpers for universal derived adjunction normalization,
compatible bases and the explicit limit complex. It opens the functor namespace
for associator notation and uses backward elaboration options for the existing
canonical complex/derived-category identifications. The preflight conservatively
classifies changes to these commands as an interface change, requiring this record.
No existing declaration signature, visibility, attribute, public import, definition,
or target statement changes. All added declarations are private and proved.

## Old

The original module had these commands before its theorem section:

```lean
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
```

Its existing `DerivedCategory.reconstruction_models` statement and the section
variables are retained verbatim. The original proof body was `by sorry`.

## New

The same commands and existing public statement remain, with these additional
file-local proof elaboration commands:

```lean
open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

The transition-comparison private helper also uses the local command prefix:

```lean
include hχ in
omit [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))] in
```

This prefix supplies the compatibility equation used by that helper and omits an
unused product instance. It ends with the private helper, before the original
`include` command and public theorem. The new proof of the original theorem is
complete. The helper definitions construct actual compatible tuples, their
coordinate differential and projections, and a limit-cone lift.

## Users

Read-only `tools/downstream.py` identifies these three downstream modules.
Only the first directly applies `DerivedCategory.reconstruction_models`.
The current claim list has no holder for any of them. No consumer adaptation is
necessary: the theorem signature and all original public imports are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels | G3 | Completes the original proof; adds private proof helpers and elaboration commands. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | unclaimed | Same theorem application and statement; no source change. |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed | Same imported theorem and definitions; no source change. |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed | Same imported theorem and definitions; no source change. |

## Status

landed 20261020T132003-L-1399619 2026-10-20 (merge of deliver/G3/Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels)
