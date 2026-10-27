# Semilinear alpha proof commands

## Reason

The new proofs need local transparency controls for the chosen adjoint and exact
localization definitions, local invertibility instances, and extra universes for
private generic category helpers. The interface checker conservatively flags the
added module commands. Every existing public declaration signature and both public
definition bodies are unchanged. No public import is changed. The additive helper
is a proved private theorem registered with a local instance attribute, not a
persistent instance for importers.

## Old

The original module has `universe u`, the existing category-theory opens, and the
variables R and φ. It has no private generic exact-localization helpers or local
irreducibility and invertibility declarations.

## New

The module has `universe u v w x`. Added options are
`linter.unusedSimpArgs false`, `backward.isDefEq.respectTransparency false`, and
`backward.isDefEq.respectTransparency.types false`. The existing synthesis bound
is retained. The new local irreducibility attribute covers moduleAlpha, moduleBeta,
moduleSquareG, moduleGComp, moduleJComp, Functor.leftAdjoint,
Functor.mapDerivedCategory, Functor.mapDerivedCategoryCompIso, and
Localization.liftNatTrans. Local instance attributes cover moduleJAdj_unit_isIso,
moduleOpenToP_isIso, and the proved private exactFunctor_of_additive helper.

These commands support the new proofs in this module. No existing statement,
definition, persistent instance, or public import is changed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SemilinearAlphaPullback --uses
alphaPullbackBeta` reports zero current Lean importers. The original item's DAG
attachment is retained: unfinished parent proofs may still need it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | R7 | Proof commands and private proved helpers added; public signatures and definitions unchanged. |

No consumer adaptation is required. No target statement or target definition changes.

## Status

landed 20261024T020102-L-2538403 2026-10-24 (merge of deliver/R7/Sheaf.AlgebraicGeometry.SemilinearAlphaPullback)
