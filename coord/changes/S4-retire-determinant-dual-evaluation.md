# AlgebraicGeometry.determinant_dual_evaluation

## Reason

Complete retirement item coord/retire-items.tsv:1789, under the human's
coord/changes/retire-sheaf-twins-20261020.md hand-off. The item currently contains
zero holes. The adopted theorem is fully proved with the same scheme, module,
rank and local-freeness hypothesis; it expresses the determinant tensor inverse
using canonical exteriorPower in place of the legacy exteriorSheaf. Their existing
comparison isomorphisms identify precisely these sheafified constructions.

The only direct consumer is
Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation (unclaimed).
Migrate its private import to the adopted ordinary theorem and add the private
ExteriorSheafPowerComparison import. Precompose the adopted evaluation ePower
with exteriorSheafPowerIso (dual M) d tensor exteriorSheafPowerIso M d. The result
has exactly the old L tensor F ≅ O_X type, so the rest of the consumer's proof,
its helpers, public imports, statement, visibility and docstring are unchanged.
No source-library module is changed. The ordinary node moves to the adopted
module and records its actual proof on exteriorPower; the shifted node records
the comparison transport in its first step. All nodes and the unit route remain.

The comparison and tensor isomorphisms apply in degree zero, on empty schemes,
and for zero section rings. No extra hypothesis or arbitrary witness is added.
The consumer import closure has no remaining import of the retired module and
no active Sheaf/upstream twin pair. Both new import directions are acyclic.
The adapted consumer compiles cleanly through lcompile.py in 23.4 seconds,
with no warning and no hole.

## Old

The retired duplicate in Sheaf.AlgebraicGeometry.DeterminantDualEvaluation:

```lean
theorem determinant_dual_evaluation (X : Scheme.{u})
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    let L : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorSheaf
        (SheafOfModules.homObj (R := X.sheaf) M
          (SheafOfModules.unit X.ringCatSheaf)) d
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorSheaf M d
    Nonempty (L ⊗ F ≅ 𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
```

Consumer private import and call:

```lean
import Sheaf.AlgebraicGeometry.DeterminantDualEvaluation
-- Inside the unchanged derived proof:
  obtain ⟨e⟩ := determinant_dual_evaluation X M d hfree
```

## New

The unchanged adopted declaration in
WeilConjectures.AlgebraicGeometry.DeterminantDualEvaluation:

```lean
theorem determinant_dual_evaluation (X : Scheme.{u})
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    let L : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorPower
        (SheafOfModules.homObj (R := X.sheaf) M
          (SheafOfModules.unit X.ringCatSheaf)) d
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorPower M d
    Nonempty (L ⊗ F ≅ 𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
```

The duplicate is withdrawn through deleted.txt. Consumer proof adaptation:

```lean
import WeilConjectures.AlgebraicGeometry.DeterminantDualEvaluation
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
-- Inside the unchanged derived proof:
  obtain ⟨ePower⟩ := determinant_dual_evaluation X M d hfree
  let e := ((Scheme.Modules.exteriorSheafPowerIso
    (SheafOfModules.homObj (R := X.sheaf) M
      (SheafOfModules.unit X.ringCatSheaf)) d) ⊗ᵢ
    (Scheme.Modules.exteriorSheafPowerIso M d)) ≪≫ ePower
```

The consumer public signature remains verbatim, on exteriorSheaf objects.

## Users

The downstream scan lists only the shifted consumer. No module imports the
retiring item after the migration; the original consumer import is invalid after
withdrawal and cannot remain as a dependency on a compiled baseline artifact.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | S4 | Retire duplicate; retain node on adopted theorem. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Migrate private import; tensor the two comparison isomorphisms. |
| WeilConjectures.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Adopted replacement; unchanged. |

## Status

landed 20261021T134536-L-1343342 2026-10-21 (merge of deliver/S4/Sheaf.AlgebraicGeometry.DeterminantDualEvaluation)
