/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates
import Sheaf.Paper.ConstructibleProjectionMates
import Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization

/-! # Expanded proper projection realization step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The expanded fixed-coordinate proper projection word used by the core identity.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-proper-projection-fixed-realization-expanded).
Proof: expand `properComponent` into the inverse proper identity, the compactification
component at `.ofIsProper`, and the proper identity at the target. The remaining
coefficient normalization and fixed-scalar counit-transpose calculation is the
lower step represented by this theorem and is left for a subsequent worker. -/
theorem properComponent_fixed_realization_expanded (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let pc :=
      ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
        component S f (.ofIsProper f.hom.left) K L ≫
        (S.finite.properIdentity f).hom.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map pc ≫
      (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
      (fixedDirect (C := C) (E := E) (n := n) f).map (targetCoordinates S f K L).hom =
    (directTensorCoordinates S f K L).hom ≫
      ((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) := by
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
  let a := directTensorCoordinates S f K L
  have hnorm := properComponent_fixed_realization_normalization S f K L
  apply (adj.homEquiv _ _).symm.injective
  rw [hnorm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
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
  simpa only [P, TX, Q, phi, pi, adj, fixedAdjunction, fixedDerivedPull, fixedTensor, fixedDirect,
    AlgebraicGeometry.ProEtale.derivedTensorRightDerivedLowerStar_obj_obj,
    AlgebraicGeometry.ProEtale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj,
    Functor.map_comp, Category.assoc] using h.symm

end WeilConjectures.CompactSupportFiniteProjection
