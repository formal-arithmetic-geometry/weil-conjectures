# AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_stratum_globalHom

## Reason

Restore the assigned quarantined module after upstream sync 5f7b33eac. The
archived proof fails at Adjunction.preservesKInjectiveComplexes because the
current criterion requires lowerStar to preserve homology. The closed-support
adjunction already supplies the required finite-colimit preservation via
closedSupport_lowerStarExact; install that existing theorem locally. Finite-limit
preservation is already an instance, so Mathlib infers preservation of homology.

## Old

The archived proof starts with:

```lean
  let A := (openImmersionLowerShriek Λ uS).obj L
  have hclosed : (closedSupport Λ i j).PreservesKInjectiveComplexes :=
    (closedSupportAdjunction Λ i j hij).preservesKInjectiveComplexes
```

## New

```lean
  let := closedSupport_lowerStarExact Λ i j hij
  let A := (openImmersionLowerShriek Λ uS).obj L
  have hclosed : (closedSupport Λ i j).PreservesKInjectiveComplexes :=
    (closedSupportAdjunction Λ i j hij).preservesKInjectiveComplexes
```

Every archived public signature, definition body, attribute, docstring, and import
is preserved. No target meaning changes. Both attached DAG nodes retain their
Lean attachments and dependencies; proof step 3 now explains this instance.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | E1 | Restore the archive and repair its proof with one local exactness instance. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed in local snapshot | Quarantined public importer; every imported signature and definition is unchanged, so no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed in local snapshot | Quarantined private importer; its stratum interface is unchanged, so no adaptation. |

The downstream tool with --allow-missing reports zero live importers and zero
uses of closedSupport_stratum_globalHom. The two quarantined importers above
were also inspected. No consumer is withdrawn or adapted, and no source-library
file is changed.

## Status

landed 20261020T152953-L-2857186 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ClosedSupportStratumHom)
