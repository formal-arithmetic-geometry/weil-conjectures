# AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoOrdinary: local proof transparency

## Reason

The new ordinary scalar/direct-image comparison needs the evaluated functor and
transition APIs of `rhoOrdinary`. Unification must use those APIs without unfolding
the chosen functor data. A local irreducibility attribute prevents that expensive
unfolding. As in the existing C8 change record
`semilinear-proper-open-proof-reducibility.md`, preflight conservatively treats the
added attribute command as an interface change and requires this record.

## Old

The existing definition, in its original scalar-restriction variable context:

```lean
def rhoOrdinary (X : Scheme.{u}) :=
  (rhoOrdinary_existsUnique C τ B φ X hφ).choose
```

No local irreducibility attribute for `rhoOrdinary` followed `rho`.

## New

The same definition remains verbatim:

```lean
def rhoOrdinary (X : Scheme.{u}) :=
  (rhoOrdinary_existsUnique C τ B φ X hφ).choose
```

After `rho`, the new proof code adds:

```lean
attribute [local irreducible] rhoOrdinary
```

This attribute affects elaboration within the item; it installs no exported
reducibility attribute. Every existing public signature, public import, public
definition body, and instance body is unchanged. The original private declaration
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.sequence_push_evaluation_normalized`
also retains its name and signature; its proof delegates to the shared private
comparison introduced before the namespace. No mathematical object or target
statement changes meaning.

## Users

`tools/downstream.py Sheaf.SixFunctors.SemilinearProperOpenMatePasting --uses
rhoOrdinary` reports zero downstream modules and only the item itself as a user
of `rhoOrdinary`. No consumer adaptation is needed. The existing DAG parents and
unit route remain in place.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | V2 | Two completed proofs; local elaboration hints only. |

No other module is edited. No target statement review is reopened by these local
proof elaboration changes.

## Status

landed 20261021T011043-L-2033859 2026-10-21 (merge of deliver/V2/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
