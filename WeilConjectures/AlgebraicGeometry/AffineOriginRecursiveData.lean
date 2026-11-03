/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOriginTowerGeometry
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionOrdinary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionProjectiveTrace
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionTensorTrace

/-! # Recursive ordinary Cartier arrows in the ordered affine tower

Source: `det-sp-trace-basic`, Proof (2), the ordered coordinate argument
(blueprint: def-sp-affine-origin-recursive-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open ProEtale.CoordinateSectionNormalization

/-- The rank-zero closed support is the identity direct image.
Source: `det-sp-trace-basic`, Proof (2), empty coordinate product
(blueprint: def-sp-affine-origin-recursive-data). -/
def affineOriginZeroSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u}) :
    (ordinaryFinitePushforward A (affineOriginTowerZeroSection S 0)).obj
        (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit A S :=
  (eqToIso (congrArg (fun f : S ⟶ S ↦
    (ordinaryFinitePushforward A f).obj (ordinaryFiniteUnit A S))
      (affineOriginTowerZeroSection_zero S))) ≪≫
    (rightDerivedLowerStarIdIso A S).app _

/-- Iterate the actual coefficient-first tensor Cartier arrows. This construction contains
no trace, adjunction transpose, or inverse trace: each successor uses only closed direct-image
composition, direct image of the previous class, and the last tensor Cartier arrow.
Source: `det-sp-trace-basic`, Proof (2), ordered cup/projection-formula calculation
(blueprint: def-sp-affine-origin-recursive-data). -/
def affineOriginRecursiveClass
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) →
    (ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
        (ordinaryFiniteUnit A S) ⟶
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
  | 0 => (affineOriginZeroSupportIso A S).hom
  | d + 1 => by
    letI := affineTraceNoetherian S d
    exact (affineOriginClosedSourceIso A S d).hom ≫
      (ordinaryFinitePushforward A
        (AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d))).map
          (affineOriginRecursiveClass A N hN hA S hS d) ≫
      affineOriginLine_class A (affineTraceTower S d) N hN hA
        (affineTraceInvertible N S hS d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))

/-- The specified compact-support source, expressed in the ordered left tower.
Source: `det-sp-trace-basic`, Proof (2), compact-support compositors
(blueprint: def-sp-affine-origin-recursive-data). -/
def affineOriginTowerSourceIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    ordinaryFiniteUnit A S ≅ (affineTraceLeft A S d).obj
      ((ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
        (ordinaryFiniteUnit A S)) :=
  affineOriginCompactSourceIso A S d ≪≫
    (affineTraceUnboundedCompactComparison A S d).symm.app _

/-- The recursive Cartier arrow with the specified compact-support source.
Source: `det-sp-trace-basic`, Proof (2), coordinate induction
(blueprint: def-sp-affine-origin-recursive-data). -/
def affineOriginRecursiveSection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (affineOriginTowerSourceIso A S d).hom ≫
    (affineTraceLeft A S d).map (affineOriginRecursiveClass A N hN hA S hS d)

end AlgebraicGeometry.Etale
