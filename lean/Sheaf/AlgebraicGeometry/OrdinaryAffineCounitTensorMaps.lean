/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
public import Sheaf.Paper.SectionLocalComparisonData
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
public import Sheaf.AlgebraicGeometry.AffineTraceTower
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Sheaf.AlgebraicGeometry.ShriekTensorComposition
public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.SixFunctors.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula

/-! # Canonical maps for tensor normalization of the ordered affine counit

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-affine-space-top-trace.proof.md,
last paragraph, expanded coefficient normalization; Stacks Project, Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization).

The geometric model is the existing ordered coordinate tower, canonically isomorphic
to affine d-space. Reassociation is constructed from the normalized line comparisons;
no isomorphism is selected from the existential right-normal-form theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace OrdinaryAffineCounitTensorNormalization

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

end OrdinaryAffineCounitTensorNormalization

end AlgebraicGeometry.Etale
