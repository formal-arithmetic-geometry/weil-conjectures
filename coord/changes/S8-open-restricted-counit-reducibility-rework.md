# AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation

## Reason

Restore the quarantined module by re-exporting the existing upstream theorem in
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation`.
The theorem's complete signature and proof body are verbatim identical to those of
our quarantined declaration. The only difference outside the copyright header is
that the upstream copy already omits the redundant local irreducibility attribute
on `derivedPullback`. Upstream declares that definition with `irreducible_def`.

Compiling the quarantined file reproduces the recorded attribute error. Removing
only that attribute compiles cleanly in 42.5 seconds and passes the delivery dry
run, but a subsequent submission compile times out at 60 seconds. Reuse the
already compiled upstream declaration instead of maintaining a duplicate proof.
No compilation limit or definition is changed. No upstream file is edited.

The existing node now attaches to that upstream declaration. Its mathematical
statement, proof steps, and proof dependency are preserved. This is reuse of an
existing complete proof, with no new theorem or assumption.

## Old

The quarantined module redeclared the following theorem, with a complete proof:

```lean
theorem singleComplexOpen_restricted_counit_cancellation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I))
```

It directly imported these modules:

```lean
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
```

It also attempted this redundant attribute:

```lean
attribute [local irreducible] derivedPullback singleComplexOpenPullbackIso
  Functor.mapHomotopyCategory Functor.mapDerivedCategory
  openPinnedHomotopyTensorRestrictionIso
```

## New

The restored module re-exports the exact same existing public theorem:

```lean
/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation

/-! # Cancelling the restricted homotopy counit comparisons

Re-export the existing upstream proof with its unchanged statement and pinned comparisons.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section

```

There is one declaration of the theorem, in the existing upstream module. Its
signature and proof body are unchanged. The node's `lean.module` and `lean.file`
now point to it, with `existing: true`.

## Users

Searches cover `lean/` and the quarantined algebraic geometry modules. No current
module imports the quarantined `Sheaf` module. `tools/downstream.py` reports it as
unknown because it is outside `lean/`. The existing upstream consumer already
imports the upstream theorem, so it needs no change. The former three public
imports remain public through the upstream module, preserving their re-exports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation | S8 | Restored as a re-export; the same theorem remains available to importers. |
| WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | Already uses the upstream declaration; unchanged. |

No target or consumer changes meaning. The exported theorem uses the same
upstream definitions and exactly the same pinned choices. No consumer adaptation
is required.

## Status

landed 20261020T150705-L-2574334 2026-10-20 (merge of deliver/S8/Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation)
