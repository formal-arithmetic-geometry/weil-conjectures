# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_local_free_comparison

## Reason

Retire the duplicate Sheaf module as assigned by coord/retire-items.tsv and the human's
2026-10-20 hand-off. The official theorem uses exteriorPower and
PresheafOfModules.exteriorPower, whereas the old callers use exteriorSheaf and
exteriorSheafPresheaf. These are propositionally equal, not definitionally equal:
the legacy restriction is chosen by uniqueness while the upstream restriction is
constructed directly. Two fully proved equality lemmas identify these constructions,
so every caller can use the official theorem without changing its signature.
No source-library file or target statement changes.

## Old

In Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison:

```lean
theorem exteriorSheaf_local_free_comparison (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((exteriorSheaf M n).over U ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin r) n))) ∧
    ∀ (V : X.Opens) (g : V ⟶ U),
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (exteriorSheafPresheaf M n)).app (op V))
```

## New

The old module is withdrawn using deleted.txt. The existing node now points at the
already proved official theorem in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison:

```lean
theorem exteriorSheaf_local_free_comparison (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((exteriorPower M n).over U ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin r) n))) ∧
    ∀ (V : X.Opens) (g : V ⟶ U),
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).app (op V))
```

New, fully proved compatibility results:

```lean
theorem exteriorSheafPresheaf_eq_exteriorPower {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n =
      _root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val n

theorem exteriorSheaf_eq_exteriorPower {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n = exteriorPower M n
```

The presheaf equality uses uniqueness of semilinear maps on pure wedges. The sheaf
equality applies the common sheafification functor to the presheaf equality. Both
cover degree zero, degrees above the rank, zero rings, and empty opens.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames | unclaimed | Replace the private comparison import by the official theorem and the required equality lemmas; rewrite the theorem conclusions back to the unchanged legacy types. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore | unclaimed | Replace the private comparison import by the official theorem and the required equality lemmas; rewrite the theorem conclusions back to the unchanged legacy types. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases | unclaimed | Replace the private comparison import by the official theorem and the required equality lemmas; rewrite the theorem conclusions back to the unchanged legacy types. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison | unclaimed | Replace the private comparison import by the official theorem and the required equality lemmas; rewrite the theorem conclusions back to the unchanged legacy types. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective | unclaimed | Remove the unused private comparison import; its chart-comparison import supplies all the facts used. |

These are all five direct importers from tools/downstream.py --direct --uses
exteriorSheaf_local_free_comparison. All five compile, as do both new modules.
There are no public-import, definition, theorem-signature, or visibility changes in
the consumers. Their existing public imports of ExteriorSheaf remain verbatim.
The shared repository's original ExteriorSheaf definitions remain unchanged; the
new lemmas prove that their meanings are exactly those of the official definitions.
The official comparison's former proof dependencies remain needed by its coordinate
proof; retirement changes the implementation location, not the mathematical route.
The main node's Lean attachment changes to that official theorem. Compatibility
nodes record the two new equalities. The four consumer nodes that use the official
comparison now record the required equality lemmas in proof and proof_deps; the
fifth node already depended only on the chart comparison and needs no change. No forced adaptation of a held module is needed.

## Status

landed 20261020T144252-L-2260026 2026-10-20 (merge of deliver/K5/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison)
