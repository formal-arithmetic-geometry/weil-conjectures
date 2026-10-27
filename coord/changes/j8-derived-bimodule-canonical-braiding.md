# ModuleCat.derivedBimoduleAdjunction, derivedBimoduleEvaluation, bimoduleClosedCurry

## Reason

Restore the module from its recorded quarantine source after upstream synchronization.
The three definitions fail to elaborate because the upstream derived braiding is now
`DerivedCategory.braidedCategory'`, an explicit definition, rather than a global instance.
Select that canonical K-flat/Koszul braiding inside each affected definition. This adds
no public instance, hypothesis, axiom, declaration or import, and preserves every signature.
The tensor and closed structures and the three formulas use the same existing structures.

The original file reports `failed to synthesize instance of type class
BraidedCategory (DerivedCategory (ModuleCat B))` at lines 67, 77 and 98. The restored,
repaired file compiles in 26.1 seconds through `lcompile.py`.

## Old

### `ModuleCat.derivedBimoduleAdjunction`

```lean
def derivedBimoduleAdjunction (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    derivedBimoduleTensor f E ⊣ derivedBimoduleHom f E :=
  ((ihom.adjunction E).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight E)).comp
    (derivedCoinductionAdjunction f)
```

### `ModuleCat.derivedBimoduleEvaluation`

```lean
def derivedBimoduleEvaluation (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B))
    (V : DerivedCategory (ModuleCat.{u} S)) :
    (derivedBimoduleTensor f E).obj ((derivedBimoduleHom f E).obj V) ⟶ V :=
  (restrictScalars f).mapDerivedCategory.map
      ((β_ E ((derivedBimoduleHom f E).obj V)).inv ≫
        (ihom.ev E).app ((derivedCoinduction f).obj V)) ≫
    (derivedCoinductionAdjunction f).counit.app V
```

### `ModuleCat.bimoduleClosedCurry`

```lean
def bimoduleClosedCurry (X E Y : DerivedCategory (ModuleCat.{u} B)) :
    (ihom X).obj ((ihom E).obj Y) ⟶ (ihom (X ⊗ E)).obj Y :=
  MonoidalClosed.curry
    ((β_ X E).hom ▷ ((ihom X).obj ((ihom E).obj Y)) ≫
      (α_ E X ((ihom X).obj ((ihom E).obj Y))).hom ≫
      E ◁ (ihom.ev X).app ((ihom E).obj Y) ≫ (ihom.ev E).app Y)
```

## New

### `ModuleCat.derivedBimoduleAdjunction`

```lean
def derivedBimoduleAdjunction (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    derivedBimoduleTensor f E ⊣ derivedBimoduleHom f E :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  ((ihom.adjunction E).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight E)).comp
    (derivedCoinductionAdjunction f)
```

### `ModuleCat.derivedBimoduleEvaluation`

```lean
def derivedBimoduleEvaluation (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B))
    (V : DerivedCategory (ModuleCat.{u} S)) :
    (derivedBimoduleTensor f E).obj ((derivedBimoduleHom f E).obj V) ⟶ V :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  (restrictScalars f).mapDerivedCategory.map
      ((β_ E ((derivedBimoduleHom f E).obj V)).inv ≫
        (ihom.ev E).app ((derivedCoinduction f).obj V)) ≫
    (derivedCoinductionAdjunction f).counit.app V
```

### `ModuleCat.bimoduleClosedCurry`

```lean
def bimoduleClosedCurry (X E Y : DerivedCategory (ModuleCat.{u} B)) :
    (ihom X).obj ((ihom E).obj Y) ⟶ (ihom (X ⊗ E)).obj Y :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  MonoidalClosed.curry
    ((β_ X E).hom ▷ ((ihom X).obj ((ihom E).obj Y)) ≫
      (α_ E X ((ihom X).obj ((ihom E).obj Y))).hom ≫
      E ◁ (ihom.ev X).app ((ihom E).obj Y) ≫ (ihom.ev E).app Y)
```

## Users

`tools/downstream.py` with `--allow-missing` reports no active Lean importers, since
the item is quarantined. A search of both `lean/` and `quarantine/` finds the following
preserved consumer; it imports this module privately and mentions none of the changed
names in its statements or bodies. No consumer adaptation is necessary. Its quarantine
and its own rework assignment remain in place. The repaired item compiled in the
two-file overlay check (37.5 seconds), and this byte-identical consumer compiled
after it (54.1 seconds), both within the per-file limit. The unchanged consumer copy
was removed from the sandbox before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison | separate quarantined rework item; not adapted | private import retained; no use of the changed definitions; signatures unchanged |

The item's theorem and DAG attachment remain unchanged. In particular this repair does
not prove or replace `ModuleCat.derived_bimodule_tensor_hom`, and does not change a target
statement or its hypotheses. The current DAG's three newer model lemmas have no Lean
attachments; their future formalization is independent of this explicit-instance repair.

## Status

landed 20261023T123756-L-1250051 2026-10-23 (merge of deliver/J8/Sheaf.Algebra.Homology.DerivedBimoduleTensorHom)
