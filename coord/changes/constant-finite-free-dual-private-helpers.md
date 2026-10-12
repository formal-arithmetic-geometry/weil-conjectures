# constantFiniteFreeDualNaturality: private helper scope

## Reason

The stage-3 static interface checker conservatively treats the additional `open` command as interface changes. This record documents those local elaboration
commands. All added declarations are private, the monoidal instance is explicitly local,
and the existing public theorem signature and visibility are unchanged. No public definition,
statement, exported instance, or public import changes.

## Old

```lean
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme
```

The public theorem `constantFiniteFreeDualNaturality` had proof `by sorry` and no local helpers.

## New

```lean
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme
```

Within this same namespace, the proof uses `open TensorProduct`. The empty temporary
variable section left after removing the duplicate helper declarations was removed in the
second reading. Every helper declaration is private;
the constant-sheaf monoidal instance is declared `private noncomputable local instance`.
These commands make the private tensor calculations concise and affect no imported signature.
The existing theorem is now fully proved. No public declaration body other than that proof changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.ConstantFiniteFreeDualNaturality | C1 | Private local proof helpers only. |

No downstream module mentions an interface-changing declaration: the checker names only the
additional elaboration commands, not a changed declaration. Every original public signature
and public import is identical. No downstream adaptation is required or included.

## Status

landed 20261012T194103-L-452241 2026-10-12 (merge of deliver/C1/Sheaf.ConstructibleSheaf.ConstantFiniteFreeDualNaturality)
