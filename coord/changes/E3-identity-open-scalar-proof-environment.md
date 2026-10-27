# AlgebraicGeometry.Scheme.sfIdentityOpenRestriction

## Reason

The proof uses the adjunction and equivalence API. Local irreducibility prevents unfolding the
concrete sheafification and coefficient realization constructions. The new categorical helpers
use the functor namespace and opposite-category notation. These are proof-environment commands;
they do not change any declaration visible to importers. A record is supplied because the
syntactic interface gate also inspects added commands.

## Old

The original proof environment contains, verbatim:

```lean
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

There are no other option, open, or attribute commands.

## New

The original commands remain. Added commands, verbatim:

```lean
set_option backward.defeqAttrib.useBackward true
open CategoryTheory.Functor Opposite
attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction
```

The attributes are local and affect only proof elaboration in the item. The new helpers are
private and proved; their data definitions are used only by theorem proofs. The public theorem
signature and the public imports remain verbatim. The additional import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars` is private.
No target definition or statement changes, so target-meaning review is not reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction --uses
sfIdentityOpenRestriction` reports zero downstream modules and only the item's own textual use.
A direct-import search also finds no importer. No consumer adaptation is required. Unfinished
DAG parents continue to refer to the unchanged declaration and its unchanged node attachment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction | E3 | The original proof hole is filled; the proof environment changes only locally. |

## Status

landed 20261026T091417-L-3340687 2026-10-26 (merge of deliver/E3/Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction)
