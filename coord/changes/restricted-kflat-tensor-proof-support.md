# Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification proof-support commands

## Reason

Complete the six existing proof holes. Private restriction/sheafification comparisons,
tensor swaps, and coefficient maps require a helper namespace, local notation and
local reducibility/instance attributes. The static interface check records these
non-declaration commands, so this change record explicitly accounts for them.
No existing signature, definition body, public import or mathematical statement changes.
No new public declaration is introduced. All helper declarations are proved and private.

## Old

The original file has no `RestrictedTensorProof` namespace, proof-local notation,
private helper attributes, or subsequent `open RestrictedTensorProof` command.
Its shared setup is, verbatim:

```lean
set_option autoImplicit false
universe u v r wB wA wS wT
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
```

The original six theorem bodies are `by sorry`.

## New

The shared setup adds `set_option linter.unusedSectionVars false`, retaining all
original section variables and theorem signatures. The new private-helper block
starts, verbatim:

```lean
namespace RestrictedTensorProof

variable [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local irreducible] monoidalCategory cochainModulesMonoidal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" R => derivedChangeRingIndependentCoefficients J R
set_option hygiene false in
local notation "𝓻" a => (sheafCompose J (forget₂ CommRingCat RingCat)).map a
```

Local attributes make the private comparison constructions irreducible after their
computation equations are proved and register the private isomorphism proof as a
local instance. They do not change any existing global instance. The namespace is
closed before the original declarations resume. `open RestrictedTensorProof` permits
the subsequent private helpers and theorem proofs to refer to these private names.
The backward elaboration options permit comparisons between the definitionally equal
coefficient structures; they do not change any construction or hypothesis.

The six original theorem signatures remain verbatim, with complete Lean proofs.
The S-linear complex is the existing scalar-first complex, identified by the proved
B-linear tensor swap with the actual scalar-last tensor. This realizes the existing
structure's presentation interface and pure-tensor normalization unchanged.

## Users

`tools/downstream.py` finds the following complete downstream set. The only external
use is the existing restriction functor; it does not mention any new helper.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification | X8 | Six holes closed; private proof support added. Existing public interface unchanged. |
| Sheaf.Algebra.Homology.KoszulRoosProjectionComparison | X5 | No adaptation: its original public restriction and identification interfaces are unchanged. |

No target statement or target-used definition changes; no statement review is reopened
by a mathematical definition change. The independent reader can inspect every command
and verify the existing signatures against the shared source.

## Status

landed 20261021T134613-L-1391346 2026-10-21 (merge of deliver/X8/Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification)
