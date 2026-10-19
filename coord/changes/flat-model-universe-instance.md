# AlgebraicGeometry.sf_locallyBijective

## Reason

The returned delivery failed because the current library no longer determines the
auxiliary universe of `AddCommGrpCat` in `WEqualsLocallyBijective`. The proof also
uses the local restriction-flatness helper, which must be available in this file.
The repair specializes the existing published instance at auxiliary universe `0`.
This adds a named declaration with a local instance registration used while
elaborating the proofs. No existing public theorem statement, definition, or
registered global instance changes.

## Old

The returned proof relied on typeclass inference for the coefficient universe and
had no explicit local specialization:

```lean
-- no local WEqualsLocallyBijective specialization
```

## New

```lean
local instance sf_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
```

The specialization fixes the otherwise-undetermined auxiliary universe and restores
the existing restriction-flatness proof path. Its instance registration is local to
`Sheaf.SixFunctors.FlatModel`; the new name is public but has no existing users.

## Users

No consumer requires adaptation: the instance registration is local and all existing
declaration signatures and public imports stay unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FlatModel | K7 | Uses the specialized instance locally in its proofs. |

## Status

landed 20261019T192802-L-1867773 2026-10-19 (merge of deliver/K7/Sheaf.SixFunctors.FlatModel)
