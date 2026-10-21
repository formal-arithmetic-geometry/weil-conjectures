# AlgebraicGeometry.ProEtale.CondensedRing.bcoOpenAdjunction

## Reason

Restore the assigned quarantined module to its library path. The rework row records
that the merge queue reverted it after a cluster restore (2026-10-20), and preserves
its source in quarantine. Its absence is not a withdrawal. The current upstream
adjunction is still the exact construction required by the node.

## Old

The live library path is absent. The quarantined declaration is:

```lean
noncomputable abbrev bcoOpenAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j
```

## New

Restore the archived module verbatim to
`lean/Sheaf/AlgebraicGeometry/ProEtale/CondensedRing/BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias.lean`.
The declaration, all binders, visibility, and public import are identical:

```lean
noncomputable abbrev bcoOpenAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j
```

This is a source restoration, not a redefinition of the adjunction. No upstream
file, target statement, or existing DAG field changes.

## Users

The downstream script reports the live module unknown because it is absent.
An exact import/name search in both lean/ and quarantine/ finds no live consumer
and just the quarantined import below. Its source is not adapted or withdrawn.
The existing DAG attachment and all parent dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; quarantined, not edited | Restores its archived import path; no signature or semantic change. |

The module compiles alone through lcompile.py. A separate temporary `example`
checks by `rfl` that the alias is exactly the fully faithful restriction of the
ambient adjunction transported by the open-immersion derived-pullback isomorphism.
The example is removed from the delivered source.

## Status

landed 20261021T014221-L-2389073 2026-10-21 (merge of deliver/F4/Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias)
