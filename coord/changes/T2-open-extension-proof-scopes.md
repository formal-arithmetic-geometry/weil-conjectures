# OpenExtensionConstantModelConstructible proof scopes

## Reason

The proof introduces private helpers in the local CondensedRing namespace and opens
the ZeroObject notation scope for the zero constant model. These commands affect
proof elaboration only; the existing declaration signature, visibility, and public
imports are identical. No target definition or statement changes.

## Old

```lean
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
```

The theorem had a single `sorry` proof.

## New

```lean
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale
namespace CondensedRing
```

The CondensedRing namespace is closed immediately after its private proved helper.
Additional private helpers prove support vanishing and local-model transport and
construct an actual extended finite stratification. Local transparency options control elaboration of the helper and final proofs;
they do not change constants or instances visible to an importing module. The
stratification conversion is generic in a property of a scheme and its immersion;
the concrete extended stratification is passed explicitly to avoid expanding
pullback and coefficient data during kernel checking. No compile or heartbeat
limit is increased.

## Users

The read-only downstream query lists 216 transitive importers. The only direct
importer is `Sheaf.Paper.OpenImmersionLocalizing`; no module outside this item
lexically references the theorem yet. Its signature and public imports are
identical, so the consumer requires no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | T2 | private proof helpers and scopes only |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | identical imported interface; no adaptation |

## Status

landed 20261019T005425-L-2768093 2026-10-19 (merge of deliver/T2/Sheaf.Paper.OpenExtensionConstantModelConstructible)
