# AlgebraicGeometry.Scheme.CompletedScalar.completedScalarUnitAdjunction

## Reason

The stage-3 preflight conservatively classifies new `open` commands and elaboration
options as a change to what other modules see. This record documents the two additions
in Sheaf.Paper.CompletedScalarUnitAdjunction. They support the completed proof and its
private helpers. All original public imports, declaration signatures, definition
bodies, structure fields and declaration visibility are unchanged. No existing
attribute, notation, instance or source-library declaration changes.

The existing theorem's one sorry is replaced by its proof. Three new, fully proved
public helper theorems live in their own Sheaf.Paper modules and have matching DAG
nodes. No new sorry is introduced. The main module imports them only for its proof.

## Old

The original commands, verbatim, are:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme.CompletedScalar
open StrictScalarBalancing

variable {A : Type (u + 1)} [CommRing A]
```

Every original public signature and every original non-theorem body remains verbatim.
The existing theorem has the same parameters, universes and conclusion.

## New

The corresponding commands, verbatim, are:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme.CompletedScalar
open StrictScalarBalancing CompletedScalarUnitProof

variable {A : Type (u + 1)} [CommRing A]
```

The additional namespace is used to resolve strictScalarCompletionUnit from the new
proof-only import Sheaf.Paper.StrictScalarCompletionUnit. The backward-defeq option
controls elaboration of categorical comparison equations. Neither command exports
notation, changes a declaration's type or body, or changes a downstream namespace
opening. All new helpers in the existing module are private and fully proved.

No target statement or target-used definition changes meaning, so target statement
re-review is not reopened. The three new helper statements, their proofs, source
citations and DAG attachments are submitted for the normal independent CODEX review.

## Users

Read-only `tools/downstream.py Sheaf.Paper.CompletedScalarUnitAdjunction --uses
completedScalarUnitAdjunction complete Complete CompletionFacts Operations Comparison`
reports zero downstream Lean modules; each searched name occurs only in the item.
Both library roots were checked by that script. The original public API was compared
directly with the shared source and is identical. No consumer adaptation is needed.

The DAG still has a planned parent, OrderedExchangeCoefficientComparison, whose
unfinished proof cites this node. Its original dependency remains, and its expected
statement is unchanged. Zero current Lean importers is not used to withdraw anything.
The table includes this planned consumer and the new helper modules. The recorded
parent holder is K9; no claim is changed and no K9 source is included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedScalarUnitAdjunction | A9 | Original public API preserved; theorem proved using private helpers and proof imports. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 (recorded claim) | Planned DAG consumer; same theorem and definitions available; no adaptation. |
| Sheaf.Paper.StrictScalarCompletionUnit | new in A9 packet | Fully proved completion-unit comparison; only proof consumer is the item. |
| Sheaf.Paper.StrictScalarOrdinaryAdjointsExist | new in A9 packet | Fully proved ordinary derived adjunctions and normalized mate. |
| Sheaf.Paper.StrictScalarOrdinaryAdjunction | new in A9 packet | Fully proved completeness preservation; only proof consumer is the item. |

This is a source and interface check, not a downstream global build. All four delivered
modules passed the prescribed compile checks, including the delivery's full compile
check. The maintainer's global build remains responsible for landing verification.

## Status

landed 20261021T214733-L-1843231 2026-10-21 (merge of deliver/A9/Sheaf.Paper.CompletedScalarUnitAdjunction)
