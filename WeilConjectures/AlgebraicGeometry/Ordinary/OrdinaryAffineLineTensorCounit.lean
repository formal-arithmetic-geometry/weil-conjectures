/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1TensorAction
import WeilConjectures.AlgebraicGeometry.Derived.DerivedOpenCounitTensorAction
import WeilConjectures.CategoryTheory.SmoothPurity.CounitTensorPasting

/-! # Tensor counit square for one ordered affine coordinate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open OrdinaryAffineTensorActions

/-- The actual open/projective affine-line adjunction respects its specified tensor
strength and its pasted projection. Source: affine-space top trace proof, restricting
the normalized projective trace to the standard affine chart
(blueprint: lem-pur-ordinary-affine-line-tensor-counit).

Proof: apply the open counit tensor identity at the projective-line right functor.
Paste this square with ordinaryFiniteP1Counit_tensorAction. Naturality of the open
counit moves the projective strength through it. Naturality of the proper projection
then combines the two squares into the composite counit. This is exactly the
specified lineStrength and lineActionNat, so no normalization is replaced. -/
theorem ordinaryAffineLine_tensorCounit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (D : OrdinaryFiniteP1Datum A N hA t S hS)
    (H K : DerivedCategoryModule A S) :
    (lineActionNat A S H).app ((affineTraceLineRight A N hA S).obj K) ≫
      (affineTraceLineLeft A S).map (lineStrength A N hA S H K).hom ≫
      (affineTraceLineAdjunction A N hA t S hS D).counit.app
        (((ordinaryFiniteTensor A S).obj H).obj K) =
      ((ordinaryFiniteTensor A S).obj H).map
        ((affineTraceLineAdjunction A N hA t S hS D).counit.app K) := by
  let q := ProjectiveLine S ↘ S
  let j := ProjectiveLine.affineChart S
  let H' := (ordinaryFinitePullback A q).obj H
  have ho (M : DerivedCategoryModule A (ProjectiveLine S)) :=
    derivedOpenCounit_tensorAction A S H' M
  have hp := ordinaryFiniteP1Counit_tensorAction A N hA t S hS D H K
  have hc := counitTensor_pasting D.adjunction (affineTraceOpenAdjunction A S)
    ((ordinaryFiniteTensor A S).obj H)
    ((ordinaryFiniteTensor A (ProjectiveLine S)).obj H')
    ((ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} S)).obj
      ((ordinaryFinitePullback A j).obj H'))
    (fun M ↦ (ordinaryFiniteTensorPullback A j H' M).symm) K
    (properStrength A N hA S H K) (properActionNat A S H)
    (openAction A S H') (fun M ↦ ho M) hp.symm
  simpa only [lineActionNat, lineStrength, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc,
    H', j, openActionNat, affineTraceLineLeft,
    affineTraceLineRight, affineTraceLineAdjunction] using hc

end AlgebraicGeometry.Etale
