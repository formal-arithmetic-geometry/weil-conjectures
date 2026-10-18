# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_single

## Reason

The dispatcher assigned this module to C4 while the B2 landing introducing it was
present. During the proof session that entire parent landing was rolled back after a
global build failure in `Derived.UpperStarUnitCoherence`. The assigned module and
node consequently disappeared from the delivery baseline. This delivery reintroduces
only the assigned tensor-single interface, now with its complete proof, and two fully
proved local calculation modules. It does not restore the parent landing's import
changes or adapt any module held by another group.

The first preflight treats this as a new module and requires a change record, C4
creation metadata on the reintroduced node, and a report naming that node. Those
requirements are satisfied here. The original statement, source, statement
dependencies and public imports are preserved. A comparison with the original source
in the rollback repair record confirms the theorem header is identical.

## Old

The module is absent from the current post-rollback baseline. Immediately before the
rollback its declaration had this header (verbatim):

```lean
theorem boundedConstructible_tensor_single
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)
```

Its section parameters are the original commutative condensed coefficient object
`Λ`, the field `k`, and the separated finite-type structure morphism
`X : Over (Spec (.of k))`. Its proof was `by sorry`.

## New

The header above and its section parameters are unchanged. The theorem now has the
complete proof in the delivered module, from the fully proved local tensor lemmas.
The four original public imports remain exactly the same. Additional imports are
proof imports only. No existing definition or target statement changes.

The reintroduced node has the same id and the same mathematical statement as before
the rollback. Its `created` and `lean.by` fields record C4 as the worker reintroducing
it against the new baseline, and no stale B2 review marker is asserted.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle
--uses boundedConstructible_tensor_single` reports `unknown module(s)` because the
post-rollback library does not contain this module. A source search finds no current
import of the removed item or mention of its theorem. The
repaired parent may reuse the original interface without adaptation. The two new
local calculation modules have no existing consumers and are used by the delivered
assigned module. No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | C4 | Reintroduced with the original interface and complete proof. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | new in C4 delivery | New proved local tensor calculation. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | new in C4 delivery | New proved finite-free tensor calculation. |

## Status

landed 20261018T112413-L-631415 2026-10-18 (merge of deliver/C4/Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle)
