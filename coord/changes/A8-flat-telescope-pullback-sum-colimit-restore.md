# AlgebraicGeometry.flat_telescope_pullback_sum_colimit

## Reason

Restore the module quarantined by the 2026-10-20 upstream sync. The archived
public import names the retired Sheaf derived-pullback implementation; importing
it alongside the adopted DerivedAdjoint caused the reported duplicate definition.
The current Sheaf definition module is empty, so the restored statement must
publicly import the adopted source definition.

The canonical model also made implicit category and coproduct inference costly.
Specify Qh's sheaf-module carrier and the two cofan families explicitly, preserving
the elaborated statement. Reuse the existing proved countable derived-coproduct
lemma instead of elaborating four duplicate private proofs. Construct the needed
CountableAB4 instance explicitly from the sheaf category's AB4 in universe u and
the discrete equivalence between ULift J and J. The proof then uses the original
derived-adjunction and shift-preservation argument.

## Old

The module is absent from lean/ and preserved at
quarantine/Sheaf/AlgebraicGeometry/FlatTelescopePullbackSumColimit.lean.
Its relevant imports are:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
```

Its archived theorem signature is:

```lean
theorem flat_telescope_pullback_sum_colimit
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    let L := DerivedCategory.Qh ⋙ derivedPullback f
    Nonempty (IsColimit (Cofan.mk (L.obj (q.obj (∐ E)))
      (fun n ↦ L.map (q.map (Sigma.ι E n))))) ∧
    Nonempty (IsColimit (Cofan.mk (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧'))))
```

The archived module also proved the private helpers coproduct_homotopy,
derived_map_surjective, derived_map_homotopy, and derived_coproduct locally.

## New

Restore the module at its original Lean attachment, using:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Sheaf.CategoryTheory.DerivedCountableSumsExact
```

The theorem signature, with explicit inference annotations, is:

```lean
theorem flat_telescope_pullback_sum_colimit
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    let L := DerivedCategory.Qh
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⋙ derivedPullback f
    Nonempty (IsColimit (Cofan.mk (f := fun n ↦ L.obj (q.obj (E n)))
      (L.obj (q.obj (∐ E)))
      (fun n ↦ L.map (q.map (Sigma.ι E n))))) ∧
    Nonempty (IsColimit (Cofan.mk (f := fun n ↦ L.obj ((q.obj (E n))⟦(1 : ℤ)⟧))
      (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧'))))
```

The four private duplicate proofs are removed; the coproduct preservation instance
is obtained from DerivedCategory.isColimit_mapCocone_countableSum. No definition,
assumption, conclusion, binder or universe is changed. No source-library module
or target signature changes. A scratch compatibility client states the archived
signature verbatim and proves it by direct application of the restored theorem;
it compiles in 22.2 seconds. Its axiom print lists only propext, Classical.choice
and Quot.sound. The clean delivered module compiles in 19.6 seconds.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit | A8 | restored with canonical definition import, equivalent explicit statement, and proved library coproduct step |

Searches of lean/ and quarantine/ found no current Lean importers or external uses
of flat_telescope_pullback_sum_colimit, including import-all consumers of its
private helpers. The downstream tool reports unknown module because the source
is quarantined; the explicit searches include the quarantined tree.

The DAG parent lem-sc-flat-telescope-normalization-morphisms still needs exactly
this node and conclusion. Its dependency is retained. The unit
sk-thm-picard-duality has no realized attachment for this node, and its route is
preserved. Both adopted source imports and the new proved library dependency
pass import_direction.py may. KInjectiveResolution is still used transitively by
DerivedAdjoint; no upstream declaration or dependency is withdrawn.
The existing definition-review obligation for the earlier canonical
derived-pullback migration is unchanged by this restoration.

## Status

landed 20261020T221042-L-4137785 2026-10-20 (merge of deliver/A8/Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit)
