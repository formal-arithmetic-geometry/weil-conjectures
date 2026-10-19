# isomorphismTermwiseModuleInverseImage_exact

## Reason

The inherited proof used declaration-scoped options and a scoped instance removal.
The first preflight required a change record for those commands. The final proof
instead scopes both elaboration options inside its tactic body, removes the
instance-removal command, and explicitly supplies local abelian sheafification
and local-bijection instances. The repaired version compiles; no exported command,
statement, definition or instance changes. The added comparison import is proof-only.

## Old

```lean
theorem isomorphismTermwiseModuleInverseImage_exact {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive ∧
      PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) ∧
      PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) := by
  sorry
```

## New

```lean
theorem isomorphismTermwiseModuleInverseImage_exact {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive ∧
      PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) ∧
      PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c)
```

The signature is identical. Its proof now uses the underlying abelian natural
comparison, preservation by the inverse-image equivalence, and reflection by
the module forgetful functor. Both options are inside the proof only.

## Users

`tools/downstream.py Sheaf.Paper.IsomorphismDerivedPullback --uses
isomorphismTermwiseModuleInverseImage_exact` reports one module using this name:
the item itself (the theorem and three derived instances).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismDerivedPullback | C4 | Proof completed; signature unchanged. |

The three instances keep their original signatures and proof bodies. All other
808 downstream modules see the identical interface. No target definition or
statement changes, so no target statement review is reopened.

## Status

landed 20261019T002515-L-2143751 2026-10-19 (merge of deliver/C4/Sheaf.Paper.IsomorphismDerivedPullback)
