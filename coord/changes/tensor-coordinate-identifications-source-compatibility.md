# exists_tensor_coordinate_identifications

## Reason

Restore the quarantined Sheaf module listed in coord/rework.tsv. The archive has
zero sorry holes, but compiling its exact bytes fails at line 249 with
`Unknown constant CochainComplex.isKFlat_pullback`: its private proof imports the
withdrawn Sheaf.Algebra.Homology.KFlatPullback module.

The adopted source already proves the same public theorem, using the current
source dependencies. Restore the Sheaf path as a compatibility import instead of
duplicating the theorem and its proof. Keep the existing public import of
Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison: this also preserves the
legacy IsAcyclicTensorKFlat predicate for archived consumers.

The only signature spelling difference is IsAcyclicTensorKFlat versus
IsKFlatTensor, in the hypothesis and the K-flat conclusion. Their definitions are
identical. The signature audit copies the complete archived signature under a
fresh theorem name and proves it by directly applying the adopted theorem with
all original arguments. The consumer audit copies the quarantined direct
consumer TensorStalkChainCoordinates, redirects its separately retired
SingleComplexBaseChangeStalkCondition import to the source counterpart, and
uses the repaired compatibility path in its unchanged coordinate assembly.
No mathematical hypothesis, conclusion, definition, or target is changed.

The DAG attachment points to the adopted declaration; its proof steps,
proof dependencies, source, statement and unit route are preserved. The archive
is retained. This is restoration and API deduplication, not withdrawal.

## Old

Archived public theorem signature (verbatim):

```lean
theorem exists_tensor_coordinate_identifications
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (E K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hnat : ∀ (A A' B B' : schemeDerivedCategory X) (a : A ⟶ A') (b : B ⟶ B'),
      (derivedPullback g').map (a ⊗ₘ b) ≫ τ A' B' =
        τ A B ≫ ((derivedPullback g').map a ⊗ₘ (derivedPullback g').map b))
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ E) (hP : P.IsAcyclicTensorKFlat)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P c.P) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P))
    (hχ : (derivedPullback g').map (pullbackTensorModelMap X P c.P) ≫
        (SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P c.P)) ≫
        DerivedCategory.Q.map χ.hom =
      τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj c.P) ≫
        ((SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
          (SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P)) ≫
        pullbackTensorModelMap X'
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P)) :
    let T := pullbackTensorTotal X P c.P
    let N := pullbackTensorTotal X'
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) c.N
    let d := χ.hom ≫
      HomologicalComplex.mapBifunctorMap (𝟙 _) c.t (curriedTensor _) (.up ℤ)
    ∃ (e : DerivedCategory.Q.obj T ≅ E ⊗ K)
      (e' : DerivedCategory.Q.obj N ≅ (derivedPullback g').obj E ⊗ K'),
      T.IsAcyclicTensorKFlat ∧
      IsIso ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj T)) ∧
      (SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj T) ≫
        DerivedCategory.Q.map d ≫ e'.hom =
      (derivedPullback g').map e.hom ≫ (τ E K ≫ ((derivedPullback g').obj E ◁ φ))
```

Archived imports:

```lean
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.Algebra.Homology.KFlatTensorProduct
import Sheaf.Algebra.Homology.KFlatPullback
```

## New

Complete restored compatibility module:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorCoordinateIdentifications
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Derived identifications for a specified tensor chain map

Compatibility path for the adopted source proof of
`AlgebraicGeometry.exists_tensor_coordinate_identifications`. The archived K-flat
predicate `IsAcyclicTensorKFlat` and the source predicate `IsKFlatTensor` have the
same definition, so the theorem retains its full coordinate and representation equation.

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-tensor-coordinate-identifications).
-/

@[expose] public section

```

The declaration is the existing adopted
AlgebraicGeometry.exists_tensor_coordinate_identifications in
WeilConjectures.AlgebraicGeometry.TensorCoordinateIdentifications.
The full signature is unchanged by definitional equality.

## Users

No live direct importers use the missing Sheaf module. tools/downstream.py
reports unknown module because the item is quarantined. The only archived direct
importer is listed below; it uses the public coordinate theorem, not private
helpers. No importer uses import all on the assigned Sheaf path.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates | unclaimed | Same theorem type by conversion; coordinate construction retained; audited in scratch. |

The adopted source TensorStalkChainCoordinates already imports its source
counterpart and requires no change. No source-library module is edited.

## Status

landed 20261022T002431-L-1929659 2026-10-22 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.TensorCoordinateIdentifications)
