/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.SectionLocalComparisonData
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Canonical coordinate-counit arrows on affine space

Source: main-20261015, sk-thm-dnc, Local construction, standard model;
orientation-charts Step 3 (blueprint: def-trf-coordinate-counit-arrows).

The ordered tensor-to-Tate comparison uses only the root-normalized products and even
shift comparisons. The orientation is the actual transpose of the ordered tower counit,
transported to standard affine space by its fixed coordinate isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateCounitArrows
open SectionLocalDualizingComparisons

/-- Flatness of the existing finite Tate powers, used only to compare degree-zero tensors.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-coordinate-counit-arrows).
Proof: the finite Tate line is locally free of rank one; its powers are flat. Apply the
published finite-twist theorem, with invertibility obtained by taking germs of N. -/
theorem tateFlat (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ObjectProperty.flat (Scheme.finiteEtaleTateTwist S N A hA d) := by
  sorry

/-- One canonical regrouping step for the ordered shifted Tate tensors.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-coordinate-counit-arrows). -/
@[irreducible]
def baseTateStep (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : affineLinearBaseCoefficient A N hA S d ≅
      SectionLocalDualizingComparisons.tateObject A N hA S d) :
    affineLinearBaseCoefficient A N hA S (d + 1) ≅
      SectionLocalDualizingComparisons.tateObject A N hA S (d + 1) :=
    (derivedTensorRight (ModuleCat.{u + 1} A) S
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).mapIso
        e ≪≫
      derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ (2 * (d : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
        (singleFunctorObjTensorIso _ _ (tateFlat A N hN hA S hS d) ≪≫
          (_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((Scheme.finiteEtaleTwistPullbackData A N hN hA).p S hS d 1 ≪≫
              eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N S hA)
                (Int.natCast_add d 1).symm))) ≪≫
      (eqToIso (congrArg (fun a : ℤ ↦ shiftFunctor _ a)
        (show 2 * (d : ℤ) + 2 = 2 * ((d + 1 : ℕ) : ℤ) by omega))).app _

/-- Regroup ordered shifted Tate lines, retaining the canonical pure-tensor product.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-coordinate-counit-arrows). -/
@[irreducible]
def baseTateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearBaseCoefficient A N hA S d ≅
      SectionLocalDualizingComparisons.tateObject A N hA S d :=
  Nat.rec (((shiftFunctorZero _ ℤ).app _).symm)
    (fun e ih ↦ baseTateStep A N hN hA S hS e ih) d

/-- The canonical Tate model for the tower's coefficient object.
Source: sk-thm-dnc, standard affine model (blueprint: def-trf-coordinate-counit-arrows). -/
@[irreducible]
def towerTateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d :=
  affineLinearCoefficientDescent A N hA t S hS d ≪≫
    (ordinaryFinitePullback A (affineTraceProjection S d)).mapIso
      (baseTateIso A N hN hA S hS d) ≪≫
    tatePullback A N hN hA (affineTraceProjection S d) hS
      (affineTraceInvertible N S hS d) d

/-- The actual exceptional transpose of the normalized ordered coordinate-tower counit.
Source: sk-thm-dnc, standard model (blueprint: def-trf-coordinate-counit-arrows). -/
@[irreducible]
def towerAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ⟶
      dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S d) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection S d)).homEquiv
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) (𝟙_ _)
      ((affineLinearCompactComparison N hN A hA S hS d).inv ≫
        affineTraceCounit A N hA t D S hS d ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom)

/-- The fixed coordinate isomorphism is a Cartesian map over S.
Source: sk-thm-dnc, standard model (blueprint: def-trf-coordinate-counit-arrows).
Proof: its hom is the map of the ordered coordinates, hence commutes with projection.
Cancel the isomorphism to obtain the inverse equation; a square with horizontal
isomorphisms is Cartesian. This includes the zero-variable affine space. -/
theorem standardSquare (S : Scheme.{u}) (d : ℕ) :
    IsPullback (affineTraceAffineSpaceIso S d).inv
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) (affineTraceProjection S d) (𝟙 S) := by
  sorry

/-- The prescribed affine orientation in the standard affine-space model. The middle
map is the actual tower counit's transpose; the final map is the exceptional mate
for the fixed coordinate isomorphism. No adjunction or orientation is chosen here.
Source: sk-thm-dnc, standard model (blueprint: def-trf-coordinate-counit-arrows). -/
@[irreducible]
def standardAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    SectionLocalDualizingComparisons.tateObject A N hA (AffineSpace (ULift.{u} (Fin d)) S) d ⟶
      dualizingComplex (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S ↘ S) :=
  (tatePullback A N hN hA (affineTraceAffineSpaceIso S d).inv
    (affineTraceInvertible N S hS d)
    (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) S ↘ S) hS) d).inv ≫
      (ordinaryFinitePullback A (affineTraceAffineSpaceIso S d).inv).map
        ((towerTateIso A N hN hA t S hS d).inv ≫ towerAdjoint N hN A hA t D S hS d) ≫
      dualizingComplexBaseChangeMap A (standardSquare S d)

/-- A presentation of the affine adjunction with precisely the prescribed counit at
coefficients. The condition fixes all section orientations used in this delivery.
Source: sk-thm-dnc, counit normalization (blueprint: def-trf-coordinate-counit-arrows). -/
def IsNormalized (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d) : Prop :=
  (affineDualizingIso A N hN hA S hS d adj).inv =
    standardAdjoint N hN A hA t D S hS d

end AlgebraicGeometry.Etale.CoordinateCounitArrows
