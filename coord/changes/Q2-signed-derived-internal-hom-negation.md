# CategoryTheory.RingedHomUniverses.negInt

## Reason

Expose the unchanged private integer-negation homomorphism as a reducible abbreviation.
The opposite-category shift convention uses this same homomorphism. Keeping the
abbreviation visible makes the double pullback conversion elaborate without repeated
unfolding through the concrete sheaf Hom functor. The value, type and homomorphism
law are unchanged; this private name occurs in no public statement.

## Old

```lean
private def negInt : ℤ →+ ℤ := AddMonoidHom.mk' (fun n : ℤ ↦ -n) (by intros; lia)
```

## New

```lean
private abbrev negInt : ℤ →+ ℤ := AddMonoidHom.mk' (fun n : ℤ ↦ -n) (by intros; lia)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SignedDerivedInternalHomExact | Q2 | Use the same negation in the existing ordinary shift and its double pullback conversion. |

The declaration is private. No other module imports this item with `import all`
or names this private declaration. No consumer adaptation is required.

## Status

landed 20261021T061633-L-1803618 2026-10-21 (merge of deliver/Q2/Sheaf.CategoryTheory.SignedDerivedInternalHomExact)
