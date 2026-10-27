# OrdinaryAffineCounitTensorNormalization canonical maps

## Reason

Move the five existing canonical map definitions into a public definition-only module. The new structural comparison must mention these maps while the item theorem imports that comparison, so keeping them in the item would create an import cycle. Names, universes, signatures, visibility and bodies stay verbatim. The original module publicly imports the new owner. No mathematical definition or target meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization`:

```lean
/-- One ordered reassociation step, with an arbitrary unbounded coefficient input.
Source: affine-space top trace proof, ordered coordinate tower
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization). -/
def descentStep (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : DerivedCategoryModule A S)
    (e : (affineTraceRight A N hA S d).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d))) :
    (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj
        (((ordinaryFiniteTensor A S).obj K).obj
          (affineLinearBaseCoefficient A N hA S (d + 1))) :=
  affineLinearLineDescent A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d) ((affineTraceRight A N hA S d).obj K) ≪≫
    (ordinaryFinitePullback A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).mapIso
      (ordinaryFiniteTensorRightMapIso A (affineTraceTower S d) e
        (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).symm ≪≫
      (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d))
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm) ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)).symm.app _ ≪≫
    (ordinaryFinitePullback A (affineTraceProjection S (d + 1))).mapIso
      (derivedTensorAssociator (ModuleCat.{u + 1} A) S K
        (affineLinearBaseCoefficient A N hA S d)
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧))

/-- Canonical ordered descent for every complex, extending the coefficient descent.
Source: affine-space top trace proof, ordered coordinate tower
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization). -/
def descent (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : DerivedCategoryModule A S) :
    (affineTraceRight A N hA S d).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S d)) :=
  Nat.rec (motive := fun e ↦ (affineTraceRight A N hA S e).obj K ≅
      (ordinaryFinitePullback A (affineTraceProjection S e)).obj
        (((ordinaryFiniteTensor A S).obj K).obj (affineLinearBaseCoefficient A N hA S e)))
    ((derivedTensorSingleUnitIso K).symm ≪≫
      ((affineLinearPullbackId A S).app _).symm)
    (fun e r ↦ descentStep A N hA t S hS e K r) d

/-- The actual right-functor comparison with p* K tensor A(d)[2d]. Only ordered
Tate products, even shifts and the exact inverse-image comparison occur.
Source: affine-space top trace proof, canonical Tate/shift reassociation
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization). -/
def reassociation (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    (affineTraceRight A N hA S d).obj K ≅
      (((derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower S d)).obj
        ((upperStar (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).mapDerivedCategory.obj K)).obj
        (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d)) :=
  descent A N hA t S hS d K ≪≫
    ordinaryFiniteTensorPullback A (affineTraceProjection S d) K
      (affineLinearBaseCoefficient A N hA S d) ≪≫
    ordinaryFiniteTensorRightMapIso A (affineTraceTower S d)
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).app K)
      ((affineLinearCoefficientDescent A N hA t S hS d).symm ≪≫
        CoordinateCounitArrows.towerTateIso A N hN hA t S hS d)

/-- The ordered adjunction's actual counit, transported by the specified proper/open
left comparison and the canonical right reassociation.
Source: affine-space top trace proof, ordered composite counit
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization). -/
def counit (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
      (((derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower S d)).obj
        ((upperStar (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).mapDerivedCategory.obj K)).obj
        (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d)) ⟶ K :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      (reassociation A N hN hA t S hS d K).inv ≫
    (affineDualizingTowerComparison A S d).inv.app _ ≫
    (affineTraceAdjunction A N hA t D S hS d).counit.app K

/-- The actual unit counit on W_d, with its source identified by the canonical ordered
Tate comparison. This is the original affine trace, using the unbounded left comparison.
Source: affine-space top trace proof, trace at the coefficient unit
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization). -/
def trace (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
      (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) ⟶
        ordinaryFiniteUnit A S :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      (CoordinateCounitArrows.towerTateIso A N hN hA t S hS d).inv ≫
    (affineDualizingTowerComparison A S d).inv.app _ ≫
    affineTraceCounit A N hA t D S hS d
```

## New

The preceding definitions are byte-identical in `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps`; their original owner adds `public import Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | G2 | Publicly reexports the relocated definitions; theorem statement unchanged. |

The read-only downstream scan found no other current Lean importers. Existing DAG parents retain the item node and statement. New modules use the new owner directly; no adaptation of another group's module is needed. No target definition changes, so this relocation does not change target meaning.

## Status

landed 20261025T204611-L-2980818 2026-10-25 (merge of deliver/G2/Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization)
