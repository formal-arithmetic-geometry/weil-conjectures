# SheafOfModules.systemSingleDerivedExtension

## Reason

Kernel conversion repeatedly unfolds the selected derivation merely to recover its fixed
ordinary functor and adjunction. Name the selected derivation and keep its fixed ordinary functor
and adjunction
visible through `SystemLeftExtensionDerivation.toExtension`.
The derived functor, universal comparison and normalized transpose remain the original
constructed values. This is a representation change, not an additional existence choice.

## Old

```lean
def systemSingleDerivedExtension (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemDerivedLeftExtension (systemEvaluation B n) (systemLevelKFlat B n) :=
  (Classical.choice <|
  nonempty_normalizedLeftExtension (systemEvaluation B n) (systemSingleFunctor S T B n)
    (systemSingleAdjunction S T B n) (systemLevelKFlat B n)
    (systemLevel_kFlatResolution B n) (fun f ↦ systemSingle_preserves S T B n f)).toExtension

```

## New

```lean
/-- The determined normalized derivation of the fixed ordinary singleton adjunction.
Keeping the selected derivation named prevents repeated reduction of its resolving-class
construction when comparing fields. Source: Zheng 4.1; Stacks 06XN and 0FND
(blueprint: lem-pur-system-single-derived-extension). -/
@[irreducible]
def systemSingleDerivation (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemLeftExtensionDerivation (systemEvaluation B n) (systemSingleFunctor S T B n)
      (systemSingleAdjunction S T B n) (systemLevelKFlat B n) :=
  Classical.choice <|
    nonempty_normalizedLeftExtension (systemEvaluation B n) (systemSingleFunctor S T B n)
      (systemSingleAdjunction S T B n) (systemLevelKFlat B n)
      (systemLevel_kFlatResolution B n) (fun f ↦ systemSingle_preserves S T B n f)

/-- The ordinary singleton adjunction has its everywhere-defined normalized derived
adjunction. Source: Zheng 4.1; Stacks 06XN and 0FND
(blueprint: lem-pur-system-single-derived-extension).
Proof: apply normalized derivation to the flat-term K-flat resolving class, using
the preceding resolution and invariance lemmas. -/
def systemSingleDerivedExtension (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemDerivedLeftExtension (systemEvaluation B n) (systemLevelKFlat B n) :=
  (systemSingleDerivation B n S T).toExtension
```

## Users

The textual uses inventory of `tools/downstream.py
Sheaf.CategoryTheory.SystemSingleDerivedExtension --uses systemSingleDerivedExtension`
lists the six modules below. The selected derivation is exactly the original choice term, now behind
a named
`@[irreducible]` definition. `SystemLeftExtensionDerivation.toExtension` still sets
the ordinary fields to exactly the original functor and adjunction. Derived fields
are the same determined derivation; no new data are chosen.
It applies to all indices, including zero, and all coefficient rings. Existing signatures
and target meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SystemEvaluationScalarRestrictionNormalization | F8 | Identical ordinary fields and normalized derived construction; no consumer edits required. |
| Sheaf.CategoryTheory.SystemLevelLeftExtension | unclaimed | Identical ordinary fields and normalized derived construction; no consumer edits required. |
| Sheaf.CategoryTheory.SystemSingleDerivedEvaluation | unclaimed | Identical ordinary fields and normalized derived construction; no consumer edits required. |
| Sheaf.CategoryTheory.SystemSingleDerivedExtension | unclaimed | Identical ordinary fields and normalized derived construction; no consumer edits required. |
| Sheaf.CategoryTheory.SystemSingletonGeometricPullback | F9 | Identical ordinary fields and normalized derived construction; no consumer edits required. |
| Sheaf.CategoryTheory.SystemSingletonScalarExtension | G6 | Identical ordinary fields and normalized derived construction; no consumer edits required. |

## Status

landed 20261025T143323-L-980706 2026-10-25 (merge of deliver/F8/Sheaf.CategoryTheory.SystemEvaluationScalarRestrictionNormalization)
