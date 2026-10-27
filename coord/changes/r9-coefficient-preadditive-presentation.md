# WeilConjectures.FrobeniusCoefficientTwists.coefficientPreadditive

## Reason

Name the existing native preadditive structure once. All uses in this module share
that instance presentation. Its body is exactly `inferInstance` for the unchanged
completed-coefficient module category, with no choice, proof hole or altered
addition/composition. The local instance registration does not export an instance.
This prevents repeatedly reconstructing the same large instance arguments.

## Old

No declaration; instance synthesis inserted the native SheafOfModules structure
at each use.

## New

```lean
/-- The native additive structure, retained as a named instance presentation.
Source: the existing completed-coefficient module category and Mathlib's
`SheafOfModules` preadditive instance
(blueprint: def-weil-frobenius-coefficient-twists). -/
@[instance_reducible]
def coefficientPreadditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u}) :
    Preadditive (integralTowerModules l E W) := inferInstance

```

## Users

| Module | Current holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Uses the named presentation locally; its existing data and signatures stay definitionally identical. |

There is no external consumer of this new name. Existing importers retain their
original instances. No external source adaptation is needed. The declaration is
attached to the existing coefficient-twist definition node.

## Status

landed 20261026T070903-L-3686575 2026-10-26 (merge of deliver/R9/Sheaf.Paper.FrobeniusCoefficientTwistsCanonical)
