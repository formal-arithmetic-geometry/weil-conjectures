# AlgebraicGeometry.etaleUnderivedExchange_moduleLinear (private helper and universe scope)

## Reason

The preflight conservatively classifies the added universe command as a change visible
outside the module. The new universe names parameterize a private, fully proved generic
lemma identifying the abelian map underlying a module pushforward. It avoids unfolding
restriction of scalars at each use with constant sheaves. The helper's proof is `rfl`.
No existing public signature, universe parameter, definition, instance, public import,
or target meaning changes. The helper occurs only in a public theorem's proof.

## Old

The helper was absent. The original scope commands were:

```lean
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
```

## New

The same scope commands, with the private generic API and its universe names:

```lean
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u₁ u₂ v₁ v₂

/-- Forgetting a module pushforward map gives the abelian pushforward map. -/
private theorem pushforward_toSheaf_map_for_exchange
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    {M N : SheafOfModules.{v} R} (h : M ⟶ N) :
    (SheafOfModules.toSheaf S).map ((SheafOfModules.pushforward φ).map h) =
      (F.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map
        ((SheafOfModules.toSheaf R).map h) := by
  rfl
```

The existing theorem's signature is retained verbatim. No public definition uses the
private helper, and no new global instance, notation, attribute, or public declaration
is introduced.

## Users

Ran `tools/downstream.py Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear
--uses AlgebraicGeometry.etaleUnderivedExchange_moduleLinear
AlgebraicGeometry.pushforward_toSheaf_map_for_exchange` against the shared repository.
It reports zero downstream Lean modules; the only occurrence of the public theorem is
its own declaration, and the new private helper has no existing users. The item's DAG
parents still need its unchanged statement. No consumer adaptation is necessary, and
no target statement review is reopened because no statement or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear | E2 | Same public theorem, now proved; private reflexive helper and local universe names added. |

## Status

landed 20261018T071145-L-1666257 2026-10-18 (merge of deliver/E2/Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear)
