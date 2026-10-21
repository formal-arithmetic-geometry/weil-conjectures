# Restoring the canonical integral coefficient comparisons

## Reason

The assigned rework row records that ContinuousIntegralComparisons was quarantined after
an earlier cluster restoration was reverted. The live module is absent, although its
DAG node and six parent nodes retain the mathematical obligation. Restore the archived
constructions, which already contain zero sorry proofs and compile against current APIs.
This repairs a missing definition interface, rather than closing or moving a proof hole.

## Old

The live path `lean/Sheaf/Paper/ContinuousIntegralComparisons.lean` is absent.
Its authoritative archived source is
`quarantine/Sheaf/Paper/ContinuousIntegralComparisons.lean`.
The archive defines integralScalarConstructible, integralConstructiblePullIso,
integralConstructiblePullHom, integralConstructiblePushHom,
integralConstructibleSourceHom and integralConstructibleTargetHom in namespace
AlgebraicGeometry.ProEtale.CondensedRing.

## New

Restore the complete archived module at its original live path. The source is identical
modulo whitespace: only lines longer than 100 characters are wrapped. All six declarations,
including their complete signatures and definition bodies, attributes, public imports,
universes and geometric and coefficient hypotheses are preserved. The scalar functor uses
the proved exactness and bounded constructibility preservation theorems. Pull and push
comparisons restrict the actual derivedPullIso and derivedPushHom, and source and target
comparisons compose precisely the original components. No choices or new obligations are
introduced. The DAG node, Lean attachment, proof dependencies and unit route stay unchanged.
There is no change to the meaning of a target or its definitions requiring semantic re-review.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousIntegralComparisons --allow-missing --names`
finds no live consumer. A separate import scan of both live roots and both quarantine roots
finds the five direct consumers below. The sixth row records an additional DAG parent.
All six retain the exact archived interface; none needs adaptation or is delivered here.
No local claim record exists for these consumers at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Archived direct consumer; unchanged interface. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Archived direct consumer; unchanged interface. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Archived direct consumer; unchanged interface. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Archived direct consumer; unchanged interface. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Archived direct consumer; unchanged interface. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | DAG parent; obligation and interface preserved. |

## Status

landed 20261021T020123-L-2587065 2026-10-21 (merge of deliver/G4/Sheaf.Paper.ContinuousIntegralComparisons)
