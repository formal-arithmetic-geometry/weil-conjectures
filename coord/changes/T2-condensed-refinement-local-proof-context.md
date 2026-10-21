# WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_id

## Reason

The identity refinement proof uses the pullback unit laws and their adjunction
mates. Local irreducibility keeps elaboration from unfolding the large derived
adjunction and comparison constructions during these calculations. Preflight
classifies the added `attribute` commands as an interface change and requires
this record. Every added attribute is explicitly local. All existing public
signatures, public imports, instances and construction bodies are unchanged.

## Old

```lean
theorem fieldRefinement_id {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    fieldRefinement Λ (Compactification.Refinement.id c) = 𝟙 _ := by
  sorry
```

The following two local attribute commands were absent.

## New

The theorem retains exactly the signature above and now has a complete proof
from the existing uniqueness theorem and proved pullback unit laws. The new
proof context contains:

```lean
attribute [local irreducible] fieldProperOpen fieldOpenAdjunction

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
```

The proof import is
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence`.
The added helpers, including the actual construction `fieldPushId`, are private.
These changes do not export new reducibility attributes or change any public
definition. No target changes meaning.

## Users

`tools/downstream.py Sheaf.Paper.CondensedCompactSupportProjection` reports zero
downstream modules in the shared source snapshot. The archived parent
`quarantine/Sheaf/Paper/CompactSupportCondensedRealization.lean` imports this module;
its row is retained here even though it has no live importing source. It needs no adaptation because
all public statements and definitions are unchanged and the new attributes are local.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedCompactSupportProjection | T2 | Private proof context and theorem proof only. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed in shared claim records | Quarantined parent; unchanged public interface, no adaptation. |

## Status

landed 20261021T130153-L-2584587 2026-10-21 (merge of deliver/T2/Sheaf.Paper.CondensedCompactSupportProjection)
