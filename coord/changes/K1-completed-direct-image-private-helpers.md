# WeilConjectures.CompletedCoefficientPushforward.directImage_preservesComplete

## Reason

The proof adds private helpers in the enclosing `WeilConjectures` namespace and a
local `PrincipalTransport` section with generic category variables. The static
interface checker records the extra `variable`/section/namespace commands as
"commands such as variable, open, notation or attribute" and requires this record.
The public theorem's signature and public imports are identical. There is no
change to any existing definition, hypothesis, conclusion, instance, notation,
or attribute. The helpers are private and proof-only imports remain private.

## Old

The public theorem signature, verbatim:

```lean
theorem directImage_preservesComplete (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    [hpush : (push f c).Additive] (F : RightImage (push f c))
    (K : DerivedCategory (Mod X (R l E X)))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E Y (F.functor.obj K)
```

The enclosing namespace was written as
`namespace WeilConjectures.CompletedCoefficientPushforward`, with universes `t u`.

## New

The public theorem signature remains, verbatim:

```lean
theorem directImage_preservesComplete (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    [hpush : (push f c).Additive] (F : RightImage (push f c))
    (K : DerivedCategory (Mod X (R l E X)))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E Y (F.functor.obj K)
```

The namespace is opened in two nested commands. Private helpers precede the
existing public theorem. Their local `PrincipalTransport` section declares
categories A and B and closes before the original coefficient variables are
introduced. The extra helper universes are `a av b bv`; the public declaration
still uses only `t u`. All extra declarations are private, and no extra instance
or notation is exported. No target statement or definition used by a target changes.

## Users

`tools/downstream.py ... --uses directImage_preservesComplete` finds only the
following two mentions (including the declaration itself). There are 993
transitive importers in the current source snapshot, all retaining the identical
public interface; the only direct importer is the comparison module below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedDirectImagePreservesCompleteness | K1 (assigned by dispatcher) | Private proof helpers and a complete proof replace the original hole; public signature unchanged. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed in local snapshot | The existing call in `comparison` remains verbatim and needs no adaptation; checked against the proved item. |

Validation: `lcompile.py --all` compiled the proved item in 20.8 seconds and the
original `Sheaf.Paper.CompletedCoefficientPushforwardComparison` against its
sandbox artifact in 14.1 seconds. Both passed without warnings. The unchanged
consumer copy was then removed from the sandbox; it is not delivered or withdrawn.

No consumer is modified. The item's existing DAG node changes only `proof`,
`proof_deps`, and `proof_origin`; its statement and Lean attachment stay identical.
The independent reader can check the original comparison module against the new
item without an adaptation or any changed assumptions.

## Status

landed 20261022T011853-L-3226590 2026-10-22 (merge of deliver/K1/Sheaf.Paper.CompletedDirectImagePreservesCompleteness)
