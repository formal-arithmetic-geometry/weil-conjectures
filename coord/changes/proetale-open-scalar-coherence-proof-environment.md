# Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence

## Reason

The seven theorem proofs use Mathlib's adjunction mate calculus. Its pasted-square notation needs a scoped notation opening. Marking the two large construction definitions locally irreducible keeps the proofs on their adjunction/equivalence API and prevents expensive sheafification unfolding. The stage-3 syntactic interface check treats added `open` and `attribute` commands as an interface change, so this record documents their exact scope. No declaration statement, public definition body, global attribute, or target changes.

## Old

The original module has the following proof-environment commands (verbatim):

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
```

It has no scoped TwoSquare opening or local irreducibility commands.

## New

The existing commands remain. The following commands are added verbatim:

```lean
set_option backward.defeqAttrib.useBackward true
open scoped CategoryTheory.TwoSquare
attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction
attribute [local irreducible] sfIntrinsicModuleEquivalence
```

The scoped notation is used only in this file's proof expressions. Both attributes are explicitly `local`: they do not modify the imported declarations' reducibility in consumers. The elaborator option likewise controls proof elaboration. The 13 original declaration signatures and six definition bodies are byte-identical to the original module. All new helper theorems are private and proved. Added proof imports are private. Thus no consumer's mathematical statement becomes weaker, stronger, or different, and no target-meaning review is reopened.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence --uses sfOpenRestrictionCoefficientSquare sfOpenFixedRestrictionId sfOpenCoefficientRestrictionId SfOpenRestrictionNormalized sfOpenRestriction_normalized_unique sfOpenRestriction_coefficient_comp sfOpenRestriction_coefficient_id sfOpenRestriction_cochain_comp sfOpenRestriction_cochain_id sfOpenRestrictionDerived sfOpenDerivedCoefficientRestrictionId sfOpenRestriction_derived_comp sfOpenRestriction_derived_id` reports zero downstream modules. Its textual use results contain only the item itself. No consumer adaptation is necessary. Unfinished DAG parents retain the unchanged interface and the item node's Lean attachment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence | Q9 | Seven proof holes filled; local proof environment only; signatures and definitions unchanged. |

No other module is adapted. Source-library declarations and public imports stay unchanged.

## Status

landed 20261021T120503-L-3902287 2026-10-21 (merge of deliver/Q9/Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence)
