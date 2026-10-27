# AlgebraicGeometry.FreeLogChart.coordinate and its three coordinate helpers

## Reason

Move the four explicit constructions to their own definition module so the strictly smaller
strict-local statement can use them without an import cycle through the theorem it proves.
The original theorem publicly imports the new module, preserving all names, signatures,
bodies, reducibility and visibility. Only definition ownership tags in docstrings change.
No mathematical definition or target meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.FreeLogChartOrdinaryParameters`:

```lean
namespace FreeLogChart

/-- Structural functions of the specified free chart, on the actual scheme.
Source: ILO VI 1.2, 1.6--1.7 (blueprint: lem-trf-free-log-chart-ordinary-parameters). -/
noncomputable def coordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (i : ULift.{u} (Fin r)) : Γ(W, ⊤) :=
  N.alpha.app (op (Scheme.Etale.mk (𝟙 W)))
    (β (Multiplicative.ofAdd (Pi.single i 1)))

/-- The given coordinate in the ordinary local ring, using the Zariski germ.
Source: ILO VI 1.2, 1.7 (blueprint: lem-trf-free-log-chart-ordinary-parameters). -/
noncomputable def ordinaryCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (w : W) (i : ULift.{u} (Fin r)) : W.presheaf.stalk w :=
  W.presheaf.germ ⊤ w (by trivial) (coordinate N β i)

/-- The same function in the recorded affine-colimit strict henselization.
Source: ILO VI 1.2, 1.6 (blueprint: lem-trf-free-log-chart-ordinary-parameters). -/
noncomputable def strictCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ W)
    (i : ULift.{u} (Fin r)) : Scheme.strictHenselizationRing t :=
  (strictLocalRingStrictHenselizationIso W t).hom
    (strictLocalGerm W t (Scheme.Etale.mk (𝟙 W))
      (CategoryTheory.Over.homMk t (by simp)) (coordinate N β i))

/-- Increasingly ordered indices of exactly the nonunit ordinary chart coordinates.
The list is empty when all functions are units, including when r is zero.
Source: ILO VI 1.2, 1.7 (blueprint: lem-trf-free-log-chart-ordinary-parameters). -/
noncomputable def nonunitIndices {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W)))) (w : W) :
    List (ULift.{u} (Fin r)) := by
  classical
  exact (List.ofFn (fun i : Fin r ↦ (ULift.up i : ULift.{u} (Fin r)))).filter
    (fun i ↦ ¬ IsUnit (ordinaryCoordinate N β w i))

end FreeLogChart
```

## New

In `Sheaf.AlgebraicGeometry.FreeLogChartCoordinates`, publicly re-exported by the item:

```lean
namespace FreeLogChart

/-- Structural functions of the specified free chart, on the actual scheme.
Source: ILO VI 1.2, 1.6--1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def coordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (i : ULift.{u} (Fin r)) : Γ(W, ⊤) :=
  N.alpha.app (op (Scheme.Etale.mk (𝟙 W)))
    (β (Multiplicative.ofAdd (Pi.single i 1)))

/-- The given coordinate in the ordinary local ring, using the Zariski germ.
Source: ILO VI 1.2, 1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def ordinaryCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (w : W) (i : ULift.{u} (Fin r)) : W.presheaf.stalk w :=
  W.presheaf.germ ⊤ w (by trivial) (coordinate N β i)

/-- The same function in the recorded affine-colimit strict henselization.
Source: ILO VI 1.2, 1.6 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def strictCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ W)
    (i : ULift.{u} (Fin r)) : Scheme.strictHenselizationRing t :=
  (strictLocalRingStrictHenselizationIso W t).hom
    (strictLocalGerm W t (Scheme.Etale.mk (𝟙 W))
      (CategoryTheory.Over.homMk t (by simp)) (coordinate N β i))

/-- Increasingly ordered indices of exactly the nonunit ordinary chart coordinates.
The list is empty when all functions are units, including when r is zero.
Source: ILO VI 1.2, 1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def nonunitIndices {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W)))) (w : W) :
    List (ULift.{u} (Fin r)) := by
  classical
  exact (List.ofFn (fun i : Fin r ↦ (ULift.up i : ULift.{u} (Fin r)))).filter
    (fun i ↦ ¬ IsUnit (ordinaryCoordinate N β w i))

end FreeLogChart
```

## Users

`tools/downstream.py <item> --uses <name>` was run for all four qualified names.
Each lists only the item itself. The repository has zero direct Lean importers of the
item. There is consequently no existing importer to adapt or compile against the move.
The two new consumers are compiled in this packet. Existing DAG consumers of the item
continue to use the unchanged theorem signature. Its node now names the coordinate
definition node as a statement dependency and moves the four helper attachments there.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FreeLogChartOrdinaryParameters | V2 | Publicly import the moved definitions; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.FreeLogChartCoordinates | new, V2 | Own the four constructions with the same fully qualified names and bodies. |
| Sheaf.AlgebraicGeometry.FreeLogChartStrictParameters | new, V2 | Import the coordinate definition module in its strictly smaller statement. |

## Status

landed 20261026T083242-L-2306608 2026-10-26 (merge of deliver/V2/Sheaf.AlgebraicGeometry.FreeLogChartOrdinaryParameters)
