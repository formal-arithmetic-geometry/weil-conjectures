/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData

/-! # Explicit scalar arrows on the ordered affine tower

Source: blueprint/latest, vector-bundle-purity proof paragraph 2, affine induction.
(blueprint: def-pur-vector-scalar-affine-tower-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- Tensorator, inverse pullback comparison, then the normalized shifted Tate line.
Source: scalar-descent proof Step 3
(blueprint: def-pur-vector-scalar-affine-tower-arrows). -/
def projectiveSource (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (scalarExtension φ (ProjectiveLine S)).obj
        ((ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (ordinaryFiniteP1Right B N hB S).obj ((scalarExtension φ S).obj K) :=
  (ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).hom.app
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    ((ordinaryFiniteTensor B (ProjectiveLine S)).map
      ((scalarPullbackIso φ (ProjectiveLine S ↘ S)).inv.app K)).app
        ((scalarExtension φ (ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
    ((ordinaryFiniteTensor B (ProjectiveLine S)).obj
      ((ordinaryFinitePullback B (ProjectiveLine S ↘ S)).obj
        ((scalarExtension φ S).obj K))).map
      (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))

/-- Restrict the projective source arrow to the standard affine chart.
Source: scalar-descent proof Step 2
(blueprint: def-pur-vector-scalar-affine-tower-arrows). -/
def lineSource (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S)).obj
        ((affineTraceLineRight A N hA S).obj K) ⟶
      (affineTraceLineRight B N hB S).obj ((scalarExtension φ S).obj K) :=
  (scalarPullbackIso φ (ProjectiveLine.affineChart S)).inv.app
      ((ordinaryFiniteP1Right A N hA S).obj K) ≫
    (ordinaryFinitePullback B (ProjectiveLine.affineChart S)).map
      (projectiveSource φ N hN hA hB S hS K)

/-- Iterate the actual source arrows, preserving the order of the coordinates.
Source: scalar-descent proof Step 4
(blueprint: def-pur-vector-scalar-affine-tower-arrows). -/
def towerSource (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    ∀ d : ℕ, ∀ K : DerivedCategoryModule A S,
      (scalarExtension φ (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj K) ⟶
        (affineTraceRight B N hB S d).obj ((scalarExtension φ S).obj K)
  | 0, _ => 𝟙 _
  | d + 1, K =>
    lineSource φ N hN hA hB (affineTraceTower S d)
        (affineTraceInvertible N S hS d) ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLineRight B N hB (affineTraceTower S d)).map
        (towerSource φ N hN hA hB S hS d K)

/-- Paste the compact-support scalar arrows for the standard coordinate lines.
Source: scalar-descent proof Step 4
(blueprint: def-pur-vector-scalar-affine-tower-arrows). -/
def towerLeft (φ : A →+* B) (S : Scheme.{u}) (d : ℕ) :
    affineTraceLeft A S d ⋙ scalarExtension φ S ⟶
      scalarExtension φ (affineTraceTower S d) ⋙ affineTraceLeft B S d :=
  affineTraceExchangeTower
    (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
    (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
    (fun r ↦ scalarExtension φ (affineTraceTower S r))
    (fun r ↦ compactScalarMap φ (affineTraceLineCompactification
      (affineTraceTower S r))) d

end AlgebraicGeometry.Etale.VectorTraceScalar
