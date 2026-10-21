# AlgebraicGeometry.ProEtale.CondensedRing.additive_boundedConstructibleLowerStar

## Reason

Restore the source module assigned to R4 by coord/rework.tsv. The live source path is absent;
the complete module is preserved in quarantine at the corresponding path. The rework row
records a merge-queue rollback after a cluster restore, not a mathematical withdrawal.
Restoring the four existing instances repairs this missing-source defect. The archive already
compiles against current dependencies, so its contents are restored verbatim. This is source
restoration, not a claim to have closed a proof hole or changed a definition.

## Old

The live source file is absent. The quarantined module has these four declarations, in
namespace AlgebraicGeometry.ProEtale.CondensedRing and its original variable context:

```lean
instance additive_boundedConstructibleLowerStar [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    (boundedConstructibleLowerStar Λ ℓ f).Additive := by
  unfold boundedConstructibleLowerStar
  infer_instance

instance additive_boundedConstructibleOpenImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j.left] : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Additive := by
  unfold boundedConstructibleOpenImmersionLowerShriek
  infer_instance

instance additive_boundedConstructibleLowerShriekOfCompactification
    [IsFinitenessCoefficient ℓ Λ] {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).Additive := by
  unfold boundedConstructibleLowerShriekOfCompactification
  infer_instance

instance additive_boundedConstructibleLowerShriek [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek Λ ℓ f).Additive := by
  unfold boundedConstructibleLowerShriek
  infer_instance
```

## New

Restore lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/
BoundedConstructibleAdditive.lean with exactly the quarantined contents, including the four
signatures and proof bodies above. Both public imports, all attributes, visibility, context,
docstrings and declaration names are preserved. No definition body is modified.

## Users

The source-only downstream query with --allow-missing lists the following three consumers.
The same search of quarantined Lean sources finds no additional importers. No consumer
source is changed; no existing target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Direct importer; missing source and original additivity instances restored. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; original interface restored unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; original interface restored unchanged. |

## Status

landed 20261021T014720-L-2447406 2026-10-21 (merge of deliver/R4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive)
Consumer validation is recorded in report.md. Independent delivery review and global-build
verification remain with the maintainer's pipeline.
