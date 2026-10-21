# CategoryTheory.splitPerfect_dual_torWindow: proof instance configuration

## Reason

The remote preflight classifies added `attribute` and `omit` commands as a change
in what the module exposes and requires this record. They support elaboration of
the new proof. No existing declaration signature, definition body, target statement,
public import, or global instance is changed.

Finite products of coefficient units are identified with coproducts using finite
biproducts. The standard construction of finite biproducts from finite products
must be enabled locally. The imported `RingedSiteBoundedDual.modulesHasZeroObject`
instance has a coefficient-universe parameter under `max c v r`, which inference
cannot recover. Disabling that instance for the two indicated declarations lets
Lean use the standard module-sheaf zero-object instance. The `omit` commands avoid
unused-section-instance warnings for helpers that do not require essential smallness.

## Old

There were no `attribute` or `omit` commands between the original projection
and the original theorem. Their signatures and the projection's definition body
are preserved verbatim in this delivery.

## New

The following file-local command is introduced before the private helpers:

```lean
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
```

The following scoped command prefixes the private `tensor_zero_at` helper and the
existing `splitPerfect_dual_torWindow` theorem individually:

```lean
attribute [-instance] RingedSiteBoundedDual.modulesHasZeroObject in
```

The following scoped command prefixes each of the private `split_hom_exact` and
`finitePower_dual_iso` helpers:

```lean
omit [EssentiallySmall.{max c v r} C] in
```

These commands affect local proof elaboration. They do not register a new global
instance or change any existing public statement or constructed object.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.SplitPerfectDualTorWindow --uses
CategoryTheory.splitPerfect_dual_torWindow` reported zero downstream modules and
only the declaration in its own module on 2026-10-21. Parent DAG dependencies are
preserved, including the unit's existing route; zero Lean importers is not used to
withdraw anything.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SplitPerfectDualTorWindow | A4 | Local proof elaboration; existing public signatures and projection definition unchanged. |

No other existing module is adapted. The new bounded exact-term Hom module has its
own node and adds a proved general theorem; it does not change an existing interface.

## Status

landed 20261021T140752-L-2742705 2026-10-21 (merge of deliver/A4/Sheaf.Algebra.Homology.SplitPerfectDualTorWindow)
