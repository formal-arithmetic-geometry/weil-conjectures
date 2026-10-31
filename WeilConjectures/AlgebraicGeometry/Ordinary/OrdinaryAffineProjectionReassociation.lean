/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions

/-! # Comparison of the tower tensor action with the canonical affine projection -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open OrdinaryAffineCounitTensorNormalization

/-- Pasting the specified proper/open projections and then reassociating the right
functor gives the canonical compact-support projection, with every coefficient
comparison fixed. This assertion has no counit or adjunction-data hypothesis.
Source: affine-space top trace proof, last paragraph; Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-projection-reassociation).

Proof: induct over the ordered coordinate tower. At zero, the pullback identity,
shriek identity and tensor-unit equations identify both maps. At a successor,
expand the pasted action and the pasted right strength. The proper/open projection
formula identifies the one-line action with the projection for its standard
compactification. Compactification independence transports it to the chosen shriek.
Apply compactSupportProjectionMap_comp to paste this with the preceding projection.
Pullback composition is monoidal, so its tensorator commutes with the associator
and the tensor comparison in descentStep. Naturality moves the preceding descent
and shifted-line comparison through the projection. The two inverse coefficient
descents cancel; the surviving coefficient comparison is towerTateIso inverse.
This yields the displayed equality. Only associators and the prescribed even-shift
and Tate comparisons occur; it remains valid at d zero, the empty base and zero ring. -/
theorem ordinaryAffine_projection_reassociation
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    compactSupportProjectionMap A (affineTraceProjection S d)
        (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
        (reassociation A N hN hA t S hS d K).inv ≫
      (affineDualizingTowerComparison A S d).inv.app
        ((affineTraceRight A N hA S d).obj K) =
    ((ordinaryFiniteTensor A S).obj K).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
        (CoordinateCounitArrows.towerTateIso A N hN hA t S hS d).inv ≫
        (affineDualizingTowerComparison A S d).inv.app
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≫
      (OrdinaryAffineTensorActions.action A S K d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (affineTraceLeft A S d).map
        ((OrdinaryAffineTensorActions.strength A N hA S K d
          (ordinaryFiniteUnit A S)).hom ≫
          (affineTraceRight A N hA S d).map (derivedTensorSingleUnitIso K).hom) := by
  sorry

end AlgebraicGeometry.Etale
