# CategoryTheory.Functor.exists_injectiveConeBoundaryDescent: private proof helpers

## Reason

The proof uses private helpers whose statements do not require all ambient
section instances. Scoped `omit ... in` commands keep those unnecessary
instances out of the private signatures and satisfy the unused-section-variable
linter. The static interface check records these commands conservatively as an
interface change. This record documents that flagged change: no existing public
signature, definition, attribute, import, namespace command, or section-variable
command changes. The target statements and their meanings are unchanged.

## Old

The private helpers did not exist. No existing declaration is removed or has its
statement changed. The existing public theorem had the same signature and ended
with `:= by sorry`.

## New

The added scoped commands, verbatim, are:

```lean
omit [HasDerivedCategory (ModuleCat.{m} A)] in
```

before each of `coneVector_d`, `coneVector_desc`, and `coneVector_projection`;

```lean
omit [EnoughInjectives C] in
```

before `model_chainMap`; and

```lean
omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory (ModuleCat.{m} A)] in
```

before `coneMap_vector` and `coneMap_homotopy`.
Every affected declaration is new, private, and proved without `sorry`. Each
command scopes only over the following private theorem. The existing public
theorem is proved from these helpers, Mathlib, and `exists_injectiveBoundary`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InjectiveConeBoundaryDescent | S8 | Private proof helpers only; existing public declarations unchanged. |

There are no external users of the new private helpers. No consumer requires
adaptation, since the public interface and all existing definitions are preserved.

## Status

landed 20261023T131805-L-2151947 2026-10-23 (merge of deliver/S8/Sheaf.CategoryTheory.InjectiveConeBoundaryDescent)
