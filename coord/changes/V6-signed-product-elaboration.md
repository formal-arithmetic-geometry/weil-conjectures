# SignedLineScalarTensorTower local product proof elaboration

## Reason

The remaining normalized signed-product theorem is proved by basis charts, transition
units and gluing in the actual internal Hom sheaf. Private helpers expose component
formulas rather than repeatedly unfolding slice tensor comparisons. Local reducibility
commands permit the signed-power induction and then seal the powers for the chart and
gluing calculations. These are proof elaboration settings, not exported attributes.
All existing public signatures, four definition bodies and public imports are unchanged.
No consumer or target meaning changes.

## Old

```lean
set_option allowUnsafeReducibility true in
attribute [local irreducible] scalarTensorPower signedLinePower
```

The product theorem had its complete current signature and proof `by sorry`.
The existing `tensorBasis_bijective` proof expanded the full composite of slice tensor,
two basis isomorphisms and the unitor at each use.

## New

```lean
set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower
```

This local setting precedes the proved private transition-unit lemma. Immediately after
that lemma the original irreducible setting is restored. All helpers are private, fully
proved, and occur only in theorem proofs. The generic tensor-to-unit chart has its own
proved pure-tensor computation; the basis lemma applies this computation on the slice.
A proof-only import supplies existing local-bijectivity detection lemmas.

## Users

`tools/downstream.py Sheaf.Paper.SignedLineScalarTensorTower --direct` reports six direct
importers. None requires adaptation because the public interface is identical.
The new private helpers have no external users.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SignedLineScalarTensorTower | V6 | Complete remaining theorem; private proof helpers. |
| Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison | not adapted | Identical interface. |
| Sheaf.Paper.IntegralLinePowerComparisons | not adapted | Identical interface. |
| Sheaf.Paper.SignedLinePullbackNormalization | not adapted | Identical interface. |
| Sheaf.Paper.SignedLineScalarPullbackSquare | not adapted | Identical interface. |
| Sheaf.Paper.SignedTwistSiteTransport | not adapted | Identical interface. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | not adapted | Identical interface. |

## Status

landed 20261024T234306-L-2551027 2026-10-24 (merge of deliver/V6/Sheaf.Paper.SignedLineScalarTensorTower)
