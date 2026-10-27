# integral_coefficient_square_normalization proof context

## Reason

Keep elaboration of the new private proofs at their categorical interfaces, rather than unfolding scalar extension, inverse-image constructions and the continuous scalar map. The settings and local attributes affect this module's proof checking only. Existing public statements, definition bodies, visibility and public imports are unchanged.

## Old

The original module has no proof-local commands between `IntegralAssertions` and the final theorem, and its final theorem has proof `by sorry`.

## New

```lean
attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp upperStar
attribute [local irreducible] FiniteConstantModel.scalarToContinuous
set_option backward.isDefEq.respectTransparency.types false
```

A private `pointScalar` wrapper has the explicit type `constantPoint A ⟶ Profinite.continuousCoefficientRingObj A` and body `FiniteConstantModel.scalarToContinuous A`. Its private monoid-homomorphism instance is the existing instance. Giving this same map an explicit endpoint prevents the kernel from unfolding the sheafification construction during concrete naturality checks.

The final conjunction is assembled in a proved private lemma over an abstract coefficient ring, then specialized to the p-adic coefficient integers. This keeps kernel checking of the generic assembly separate from unfolding the concrete coefficient construction.

Private helpers with complete proofs replace the final theorem's `sorry`. Proof-only imports provide existing theorems and constructions. No option or attribute is exported, and no definition is replaced.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralCoefficientSquareNormalization` reports zero downstream modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | Y8 | Its one hole is filled, with local proof elaboration support. |

## Status

landed 20261024T022547-L-3005716 2026-10-24 (merge of deliver/Y8/Sheaf.Paper.IntegralCoefficientSquareNormalization)
