/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionFixedCoordinates
import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.FiniteProperProjectionFixedRealizationNormalizationCore

/-! # Proper projection coordinate normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/--
The transpose of the expanded proper-coordinate composite is the fixed-scalar
tensor/counit composite.  This is the coefficient normalization part of the
proper-factor calculation; the final identification with the published
projection map is the generic right-adjoint projection identity.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-proper-projection-fixed-realization-normalization).
Proof: expand the proper identity, compactification component, and coordinate
comparisons.  Apply the finite proper normalization and the normalized direct
adjunction counit, then cancel the coefficient-equivalence units and use
naturality of the fixed tensor comparison.  The resulting transpose is the
fixed pullback tensor comparison followed by the fixed counit. -/
theorem properComponent_fixed_realization_normalization
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let pc :=
      ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
        component S f (.ofIsProper f.hom.left) K L ≫
        (S.finite.properIdentity f).hom.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))
    let JX := coordinates (C := C) (E := E) (n := n) (hn := hn) X
    let JY := coordinates (C := C) (E := E) (n := n) (hn := hn) Y
    let P := fixedDerivedPull (C := C) (E := E) (n := n) f
    let Q := fixedDirect (C := C) (E := E) (n := n) f
    let adj := fixedAdjunction (C := C) (E := E) (n := n) f
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let N := (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj
    let phi := AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      f.hom.left
    ((adj.homEquiv _ _).symm
      ((JY.map pc ≫
        (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
        Q.map (targetCoordinates S f K L).hom))) =
      P.map (directTensorCoordinates S f K L).hom ≫
        (phi.app (Q.obj (JX.obj K))).app N ≫
        (TX.map (adj.counit.app (JX.obj K))).app (P.obj N) := by
  let _ := Padic.finite_coefficientExtensionRing C.l E n hn
  let JX := coordinates (C := C) (E := E) (n := n) (hn := hn) X
  let JY := coordinates (C := C) (E := E) (n := n) (hn := hn) Y
  let P := fixedDerivedPull (C := C) (E := E) (n := n) f
  let Q := fixedDirect (C := C) (E := E) (n := n) f
  let adj := fixedAdjunction (C := C) (E := E) (n := n) f
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let N := (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj
  let phi := AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left
  let pi := AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left
  let pc :=
    ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
      component S f (.ofIsProper f.hom.left) K L ≫
      (S.finite.properIdentity f).hom.app
        (((partialTensor S X).obj K).obj ((torPull S f).obj L))
  dsimp
  rw [Adjunction.homEquiv_symm_apply]
  have hcoord := properComponent_fixed_realization_coordinate_projection S f K L
  rw [hcoord]
  simp only [Functor.map_comp, Category.assoc]
  have hpi := AlgebraicGeometry.ProEtale.map_rightDerivedLowerStarProjectionMap_comp_counit
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left (JX.obj K) N
  have hpi' :
      P.map ((pi.app (JX.obj K)).app N) ≫ adj.counit.app
          ((TX.obj (JX.obj K)).obj (P.obj N)) =
        (phi.app (Q.obj (JX.obj K))).app N ≫
          (TX.map (adj.counit.app (JX.obj K))).app (P.obj N) := by
    change P.map ((pi.app (JX.obj K)).app N) ≫ adj.counit.app
          ((TX.obj (JX.obj K)).obj (P.obj N)) =
        (phi.app (Q.obj (JX.obj K))).app N ≫
          (TX.map (adj.counit.app (JX.obj K))).app (P.obj N) at hpi
    exact hpi
  have h := congrArg (fun t ↦ P.map (directTensorCoordinates S f K L).hom ≫ t) hpi'
  simpa only [P, TX, Q, phi, pi, JX, N, adj, fixedAdjunction, fixedDerivedPull,
    fixedTensor, fixedDirect,
    AlgebraicGeometry.ProEtale.derivedTensorRightDerivedLowerStar_obj_obj,
    AlgebraicGeometry.ProEtale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj,
    Functor.map_comp, Category.assoc] using h

end WeilConjectures.CompactSupportFiniteProjection
