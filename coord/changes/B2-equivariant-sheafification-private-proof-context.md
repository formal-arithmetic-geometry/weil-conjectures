# CategoryTheory.InternalActionSite.equivariantModuleSheafification_reflector

## Reason

The proof uses a local section and variable commands to share parameters among
private, completely proved helpers. The static command gate requires this record.
These commands do not alter any public declaration or importer-visible notation,
instance, attribute, option, or import. Every helper is private. No consumer needs
adaptation. The private redundant Sheafification import is removed.

## Old

```lean
namespace CategoryTheory.InternalActionSite
```

The theorem followed directly, with a sorry proof. Its signature, universes,
visibility, and docstring are preserved verbatim by this delivery.

## New

```lean
namespace CategoryTheory.InternalActionSite

section ActionConstruction

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : Cᵒᵖ ⥤ GrpCat.{u}) (R : Sheaf J RingCat.{u})
  (P : EquivariantPresheaf K R.obj)

end ActionConstruction
```

Private helpers inside the section construct the induced action and reflector.
The option `backward.isDefEq.respectTransparency false` is scoped to individual
private declarations. It changes elaboration only, never a public signature.
The existing public theorem now has a complete proof assembled from those helpers.

## Users

`tools/downstream.py` lists two downstream modules; declaration-specific search
lists only the item itself, because neither downstream module calls this theorem
in its current proof. All their statements keep the same meaning and every existing
public declaration of the item retains its exact signature. No adapted module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector | B2 | Proof completed; public interface unchanged |
| Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful | unclaimed | Private proof import; no interface change |
| Sheaf.CategoryTheory.CondensedTensorInductionAdjunction | unclaimed | Private proof import; no interface change |

## Status

landed 20261023T123331-L-1163001 2026-10-23 (merge of deliver/B2/Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector)
