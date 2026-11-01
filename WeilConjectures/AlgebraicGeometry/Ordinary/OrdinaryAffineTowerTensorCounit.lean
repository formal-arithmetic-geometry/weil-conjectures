/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineLineTensorCounit
import WeilConjectures.CategoryTheory.SmoothPurity.CounitTensorTower

/-! # Tensor counit square for the ordered affine tower -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open OrdinaryAffineTensorActions

/-- The ordered affine adjunction has the tensor counit square obtained by pasting
its coordinate squares. Source: affine-space top trace proof, ordered induction
(blueprint: lem-pur-ordinary-affine-tower-tensor-counit).

Proof: apply counitTensor_tower with coefficient endofunctor tensoring on the left
by the ordered pullback of H. At coordinate e, ordinaryAffineLine_tensorCounit is
exactly the required one-step square. The tower definitions give the pasted action
and strength. No equation asserting determination of a map by its unit value is used. -/
theorem ordinaryAffineTower_tensorCounit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (H K : DerivedCategoryModule A S) :
    (action A S H d).app ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLeft A S d).map (strength A N hA S H d K).hom ≫
      (affineTraceAdjunction A N hA t D S hS d).counit.app
        (((ordinaryFiniteTensor A S).obj H).obj K) =
      ((ordinaryFiniteTensor A S).obj H).map
        ((affineTraceAdjunction A N hA t D S hS d).counit.app K) := by
  unfold action strength affineTraceAdjunction
  apply counitTensor_tower
  intro e M
  let := affineTraceNoetherian S e
  exact ordinaryAffineLine_tensorCounit A N hA t (affineTraceTower S e)
    (affineTraceInvertible N S hS e) (D _ _) ((pull A S e).obj H) M

end AlgebraicGeometry.Etale
