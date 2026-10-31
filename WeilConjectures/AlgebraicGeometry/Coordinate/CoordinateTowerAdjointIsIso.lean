/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction

/-! # Invertibility of the ordered affine tower counit transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem compactComparison_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    _root_.DerivedCategory.Plus.ι.map
      ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app
      (_root_.DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

/-- The exceptional transpose of the ordered affine tower counit is invertible.
Source: sk-thm-dnc, Local construction, affine-space adjunction
(blueprint: lem-trf-coordinate-tower-adjoint-isomorphism).

Proof: The bounded compact-support comparison at the coefficient object is the
restriction of the unbounded comparison. Transport the ordered tower adjunction along
that comparison. The canonical exceptional adjunction has the same left functor, so
uniqueness of right adjoints gives an isomorphism between their right functors. At the
constant coefficient, its component followed by the exceptional functor applied to the
single/derived-unit isomorphism is exactly the defining transpose of the tower counit.
Both factors are isomorphisms. This argument includes the zero-dimensional tower.
-/
theorem coordinateTowerAdjoint_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    IsIso (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) := by
  let a := (affineTraceAdjunction A N hA t D S hS d).ofNatIsoLeft
    (affineTraceUnboundedCompactComparison A S d)
  let b := rightDerivedUpperShriekAdjunction A
    (affineTraceProjection S d)
  have he : CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d =
      (a.rightAdjointUniq b).hom.app (ordinaryFiniteUnit A S) ≫
        (rightDerivedUpperShriek A (affineTraceProjection S d)).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom := by
    unfold CoordinateCounitArrows.towerAdjoint
    rw [compactComparison_eq N hN A hA S hS d]
    rw [← Category.assoc, b.homEquiv_naturality_right]
    congr 1
    apply (b.homEquiv _ _).symm.injective
    exact (Equiv.symm_apply_apply _ _).trans
      (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app a b
        (ordinaryFiniteUnit A S)).symm
  rw [he]
  infer_instance

end AlgebraicGeometry.Etale
