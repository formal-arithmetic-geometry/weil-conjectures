# CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedActionRealization

## Reason

The proof uses composition preservation of finite limits and colimits for the
exact-functor derived comparison API. Register the existing composition lemmas
as local instances in this module. The static interface scan flags this added
attribute command. It creates no new mathematical hypothesis or public instance;
the theorem signature and the public imports are unchanged.

## Old

No local attribute command followed the namespace opening:

```lean
namespace CategoryTheory.Endofunctor.IsoAlgebra
```

## New

```lean
namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The added recursive abbreviations and lemmas are private proof helpers. The
fixed-pair complex is constructed degreewise; all properties have complete proofs.
No existing definition, declaration signature, visibility or public import changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CyclicDerivedActionRealization | G5 | Local instance search supports the proof. |

`tools/downstream.py Sheaf.CategoryTheory.CyclicDerivedActionRealization --uses
exists_cyclicDerivedActionRealization` reports zero downstream modules and only
this module's own declaration occurrence. No consumer adaptation is needed. DAG
parents with unfinished proofs retain the unchanged theorem and its attachment.

## Status

landed 20261023T102751-L-2969060 2026-10-23 (merge of deliver/G5/Sheaf.CategoryTheory.CyclicDerivedActionRealization)
