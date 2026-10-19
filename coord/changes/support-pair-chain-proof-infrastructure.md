# CategoryTheory.supportPairChainCoherence proof infrastructure

## Reason

The chain-map and homotopy proof needs additive evaluation and canonical
continuous pushforward. The two private instances below provide these concrete
properties. The declaration-local `omit` commands avoid unused-section-variable
warnings in private lemmas; declaration-local transparency options let Lean
identify evaluations of mapped complexes. Server preflight requires this record
because its interface scan flags additions of instances and scope commands.

Every existing public signature, definition body, docstring, universe and import
is unchanged. The new constructions and lemmas are private proof helpers for the
existing five DAG steps. They contain no holes or arbitrary data choices. No
target or consumer statement changes meaning, so no target statement review is
reopened and no consumer adaptation is necessary.

## Old

The module has no `sectionFunctor_additive` or `pairPushforward_additive`
instance and no private proof-helper declarations. The existing theorem ends:

```lean
  sorry
```

## New

```lean
private instance sectionFunctor_additive (J : GrothendieckTopology C) (X : C) :
    (sectionFunctor J X).Additive where

private instance pairPushforward_additive (u : C ⥤ D) [u.IsContinuous Jc Jd] :
    (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd).Additive where
```

Both proofs are definitional instances of additivity. The theorem's complete
proof uses degreewise adjoints, evaluation, kernel lifts and compatible
homotopies, followed by the existing K-injective Mathlib comparison. All helper
statements are private; each `omit` or transparency option has the scope of its
following private declaration. The original theorem has zero `sorry` remaining.

## Users

`tools/downstream.py Sheaf.Paper.SupportPairChainCoherence --uses
CategoryTheory.sectionFunctor` lists 208 transitive importers, with its sole
textual use in the item module. Source comparison verifies that the complete
existing definition prefix, main theorem signature and imports are identical.
The private instance names have no existing consumers. The two new instances
supply proofs of existing Prop classes, and do not replace evaluation or
pushforward data. The local commands affect only the attached private helper.
Thus no downstream statement or definition requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SupportPairChainCoherence | W4 | Complete the existing theorem using private additive instances and proof helpers; existing interface retained. |

## Status

landed 20261019T112608-L-3960370 2026-10-19 (merge of deliver/W4/Sheaf.Paper.SupportPairChainCoherence)
