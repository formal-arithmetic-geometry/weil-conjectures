# WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

## Reason

Restore the module assigned to H1 by `coord/rework.tsv`. The row records a merge-queue
rollback after a cluster restore on 2026-10-20 and preserves the source at
`quarantine/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperStarUnitCoherence.lean`.
The file is absent from the live library, despite a surviving public importer.
Restoration repairs that missing source; it does not remove or weaken a declaration.

## Old

The live module path is absent. The quarantine archive contains the complete module,
with zero `sorry`s and these public imports, verbatim:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
```

Its concrete non-theorem declaration is:

```lean
noncomputable def mapHomotopyCategorySingleHom (F : C₁ ⥤ C₂) [F.Additive] {A : C₁} {B : C₂}
    (φ : F.obj A ⟶ B) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C₁ (.up ℤ)).obj
        ((HomologicalComplex.single C₁ (.up ℤ) 0).obj A)) ⟶
      (HomotopyCategory.quotient C₂ (.up ℤ)).obj ((HomologicalComplex.single C₂ (.up ℤ) 0).obj B) :=
  (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app _ ≫ (HomotopyCategory.quotient _ _).map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app A ≫
      (HomologicalComplex.single C₂ (.up ℤ) 0).map φ)
```

## New

The entire archived file is restored verbatim at its original live path. In particular the
imports and definition above, every theorem signature and proof, visibility, attributes,
section parameters and private helpers are identical to the archive. No mathematical
statement or definition changes. There is no target-meaning change, new node or new hole.
The quarantine file and all existing DAG dependencies are preserved untouched.

The module compiles cleanly against the published library in 40.1 seconds. `cmp` confirms
that the restored source is identical to the quarantine source.
The unchanged consumer also compiles against this restored module in a separate scratch
sandbox (25.4 seconds), with only its pre-existing duplicate-namespace warning at line 296.

## Users

`tools/downstream.py` reports `unknown module(s)` because the module is absent from the
live source. A search of `lean/WeilConjectures`, `lean/Sheaf` and both quarantined roots
finds the following direct consumer. Its existing call at the end of
`Slop.BorelMooreSection.integral_point` uses the unchanged pushforward unit equality.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | H1 | Restored byte-identically from quarantine, with all proofs complete. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Original import and theorem application restored; source unchanged. |

## Status

landed 20261021T020124-L-2587506 2026-10-21 (merge of deliver/H1/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence)
