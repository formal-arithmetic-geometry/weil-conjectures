# AlgebraicGeometry.ProEtale.SemilinearProperOpen.evaluationPush_transition

## Reason

The proof compares the carriers of evaluation and module direct image. Local
irreducibility settings prevent Lean from expanding constant sheafification and
the constant-ring isomorphism while checking these carriers. Preflight detects
changed attribute commands conservatively and requests this record. All added
attributes use `[local irreducible]`: they affect elaboration of this module
only. No public signature, definition body, public import or persistent attribute
changes, and no target statement or meaning changes.

## Old

```lean
attribute [local irreducible] coefficientMap proEtaleConstantDirectImageMap evaluationPush
```

The three theorems had their existing unchanged signatures and `by sorry` proofs.

## New

```lean
attribute [local irreducible] constantSheaf
attribute [local irreducible] coefficientMap proEtaleConstantDirectImageMap
  evaluationCoefficientDirectImage proEtaleRingDirectImageMap
attribute [local irreducible] evaluationPush push StrictTower.constantRingIso
  proEtaleConstantInverseImageMap
```

The same three signatures now have complete proofs. Added helpers are private,
proved lemmas. The `import all` and `Mathlib.Logic.Function.Basic` imports are
private proof imports. Three redundant private imports are removed. No
consumer adaptation is required.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearEvaluationRingSquare | J2 | Three holes filled; local proof settings only. |
| Sheaf.SixFunctors.SemilinearEvaluationOrdinaryAdjunction | unclaimed | Still applies the unchanged `evaluationPush_existsUnique`; no change required. |

`tools/downstream.py` lists only the latter downstream module. Searches for all
public names find no other external use. Public statements and all public
definitions remain verbatim, so the downstream application and targets keep
their meanings.

## Status

landed 20261023T231630-L-3627949 2026-10-23 (merge of deliver/J2/Sheaf.SixFunctors.SemilinearEvaluationRingSquare)
