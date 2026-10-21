# System tensor mate local proof settings

## Reason

The assembly proofs introduce a private ordinary-operations construction.
Unfolding arbitrary adjoint choices and derived functors during elaboration
causes excessive reduction. Local irreducibility keeps these constructions
abstract while their public APIs supply the needed equations and instances.
The preflight command fingerprint requires a change record for these local
attribute commands.

## Old

The current item has two theorem holes and no `ordinaryOperations` helper.
It has no local irreducibility attributes for `Functor.leftAdjoint`,
`Functor.mapDerivedCategory` or `Functor.rightDerivedFunctor`.

## New

The new proof-local commands are:

```lean
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local irreducible] ordinaryOperations
```

The first command precedes the private ordinary-operations construction;
the second follows it. Both scopes end with the module. These commands change
proof elaboration only. The private helper constructs actual operations from
the existing semilinear calculus and varying-ring adjunctions; it contains no
hole. Every existing public signature, definition body, public import,
visibility and global instance attribute is preserved.

The two original theorem proofs are complete, using two new proof-only imports
with independent geometric lemmas. Each of these lemmas has one named theorem
hole, its own module and node. The report records this as a decomposition with
net zero holes closed, not as a complete proof of the two geometric lemmas.
No adopted source-library module is edited.

## Users

| Module | Current holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.SystemTensorMateArrows | R3 | Proofs and private support only. |
| Sheaf.Paper.FiniteFreeCompactComposition | Unchanged consumer | Public interface preserved. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Unchanged consumer | Public interface preserved. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | Unchanged consumer | Public interface preserved. |

The latter three consumers are quarantined and preserved. No consumer source
is adapted. No target statement review reopens: no existing definition or
statement meaning changes.

## Validation

All three sandbox modules compile through `lcompile.py --all`. The complete
item compiled in 47.7 seconds in the final profiled check. The delivery compiler
check also passed before the metadata corrections recorded here.

## Status

landed 20261021T005747-L-1889254 2026-10-21 (merge of deliver/R3/Sheaf.Paper.SystemTensorMateArrows)
