# CategoryTheory.homTensorLocalized_ext

## Reason

The proof needs tensor-Hom transposition at independent site universes. The existing source
API specializes all universes to one. Fully proved private helpers supply the same elementary
construction at the required universes. The static preflight flags the new namespace-local
`open` and `variable` commands as an interface change, requiring this record. There is no
public signature, definition, instance, import or visibility change. Helper simp attributes
are local, and all helper declarations are private. No other module requires adaptation.

## Old

No `CategoryTheory.LocalTensorHom` helper namespace. The existing theorem has its original
signature and proof `:= by sorry`.

## New

The new private helper namespace starts with:

```lean
namespace LocalTensorHom

open PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
```

Each helper lemma additionally states these binders explicitly in its own signature,
including the independent site universes `u` and `v`. This follows the returned landing
check X-1b6a5: its textual comparison omitted surrounding `variable` declarations and
therefore mistook these generalized statements for the source single-universe statements.
The explicit signatures document the actual difference and introduce no new API.

Every declaration inside is private and fully proved; its simp attributes are local. The
namespace closes before the unchanged ambient variables and theorem signature. The theorem
now has a complete proof. Its heartbeat increase is scoped to that theorem only.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.HomTensorLocalizedExt --uses homTensorLocalized_ext`
finds the item and its one direct user listed below. There are 389 transitive importers; they
are unaffected because the helper namespace exposes no new public API, all commands are
namespace-scoped or declaration-scoped, and the existing public statement and import stay
identical. No user statement becomes weaker, stronger or different.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomTensorLocalizedExt | P1 | Existing theorem proved; signature unchanged. |
| Sheaf.Algebra.Homology.HomTensorNaturalityComponent | unclaimed | Existing application unchanged. |

## Status

landed 20261013T062527-L-734371 2026-10-13 (merge of deliver/P1/Sheaf.Algebra.Homology.HomTensorLocalizedExt)
