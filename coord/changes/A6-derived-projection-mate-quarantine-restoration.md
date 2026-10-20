# AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison

## Reason

The assigned module is quarantined under coord/rework.tsv after the upstream sync:
its public Sheaf.DerivedPullback import collided with the upstream derivedPullback
already imported through its other dependencies. Restore the module as a public
compatibility import of its canonical upstream counterpart, and reattach its DAG node
to that existing declaration. This supplies the actual theorem rather than an empty
module or a fresh copy of the same public declaration.

The archive and upstream theorem signatures and complete proof bodies compare
byte-for-byte equal. No source-library file is changed. All three proof dependencies,
the mathematical statement, localization universes, and unit route are retained.

## Old

The quarantined module contained this declaration, on the old mixed import graph:

```lean
theorem exists_derivedProjectionMate_openRestriction_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X)
    (U : Y.Opens)
    (Z : Scheme.{u}) (g : Z ⟶ U.toScheme)
    (hZ : Z = (f ⁻¹ᵁ U).toScheme) (hg : HEq g (f ∣_ U)) :
    letI : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
        inferInstance
    letI : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) := inferInstance
    ∃ (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
        (s : tensor (schemeDerivedCategory U.toScheme) ⋙ derivedPullback g ≅
          (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory Z))
        (N : schemeDerivedQCohCategory U.toScheme) (E : schemeDerivedQCohCategory Z),
        Nonempty (Arrow.mk ((schemeOpenRestriction Y U).mapDerivedCategory.map
          (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
            ((derivedPullback f).obj M.obj ⊗ L.obj)
              (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
                (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))) ≅
          Arrow.mk (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
            ((derivedPullback g).obj N.obj ⊗ E.obj)
              (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
                (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj))))
```

Its six public imports were:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Comma.Arrow
```

## New

Restore the assigned module with:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison
```

The re-exported theorem has exactly the signature quoted above. The DAG's lean record
now names that upstream module, the same declaration, and the same statement text.
The upstream module publicly imports the same prerequisites, using the canonical
upstream DerivedPullback. The three old private proof imports are still used by the
upstream theorem and remain in the DAG proof_deps. No mathematical node is pruned.

## Users

No current Lean file imports the quarantined Sheaf path. The declaration's two
external textual users already import the upstream counterpart, so no adaptation is
necessary. tools/downstream.py rejects the absent Sheaf module as unknown; a source
scan of lean and quarantine verifies that it has no direct importers. The upstream
module and its 205 transitive consumers are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison | A6 | Restore public access to the canonical theorem. |
| WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison | unchanged | Existing source and proof remain verbatim. |
| WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartTransport | unchanged | Already uses the canonical theorem; no edit. |
| WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses | unchanged | Already uses the canonical theorem; no edit. |

All DAG parents continue citing the same node, whose existing proof and dependencies
are preserved. This is restoration and canonical attachment, not withdrawal.

## Status

landed 20261020T211620-L-3479048 2026-10-20 (merge of deliver/A6/Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison)
