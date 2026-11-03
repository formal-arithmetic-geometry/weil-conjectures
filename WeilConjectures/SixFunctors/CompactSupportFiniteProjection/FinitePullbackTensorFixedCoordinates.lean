/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionFixedCoordinates

/-! # Pullback tensor comparison in fixed coefficient coordinates

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

attribute [local irreducible] realization AlgebraicGeometry.ProEtale.derivedTensor

private theorem map_inverse_cancel {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {U V : A} (e : U ≅ V) {W : B} (g : W ⟶ F.obj V) :
    g ≫ F.map e.inv ≫ F.map e.hom = g := by
  rw [← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Checking the explicit realization composites requires additional elaboration heartbeats.
/-- The prescribed pullback/tensor comparison in fixed coefficient coordinates.
Source: prop-sf-pf-coherence, proper-factor paragraph, and the explicit construction
of pullbackTensorComparison (blueprint: lem-sf-finite-pullback-tensor-fixed-coordinates).
Proof: expand pullbackTensorComparison as the pullback realization followed by the
coefficient realization of the fixed scalar tensor pullback comparison. Apply the inverse
realization. Naturality of its inverse unit moves the inner fixed scalar map past the
unit. The second-input fixed pullback comparison and its inverse cancel after applying
tensor in that input. The first-input comparison remains inverted. Functoriality and
associativity give exactly the displayed composite. No properness, counit, projection,
or finite Tor condition on the first input is used. Zero objects and empty schemes use
the same unit and isomorphism identities. -/
theorem pullbackTensor_fixed_coordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        (pullbackTensorComparison S f M L).hom ≫
      (targetCoordinates S f ((S.finite.pull f).obj M) L).hom =
    (fixedPullRealization S f (((partialTensor S Y).obj M).obj L)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (tensorCoordinates S Y M L).hom ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) Y).obj M)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) ≫
      ((fixedTensor (C := C) (E := E) (n := n) X).map
        (fixedPullRealization S f M).inv).app
          ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
            ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let P := fixedDerivedPull (C := C) (E := E) (n := n) f
  let A := ((partialTensor S Y).obj M).obj L
  let a := pullRealization S f A
  let b := fixedPullRealization S f M
  let c := fixedPullRealization S f ⟨L.obj, L.property.1⟩
  let q := (fixedPullComparison (C := C) (E := E) (n := n) f).symm.app
    (RY.inverse.obj A.obj)
  let m := AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      f.hom.left (RY.inverse.obj M.obj) (RY.inverse.obj L.obj)
  let t := q ≪≫ P.mapIso (tensorCoordinates S Y M L) ≪≫ m ≪≫
    (TX.mapIso b.symm).app (P.obj (RY.inverse.obj L.obj)) ≪≫
    (TX.obj (RX.inverse.obj ((S.finite.pull f).obj M).obj)).mapIso c.symm
  have h : (pullbackTensorComparison S f M L).hom.hom =
      a.hom ≫ RX.functor.map t.hom := rfl
  change RX.inverse.map (pullbackTensorComparison S f M L).hom.hom ≫
      RX.unitIso.inv.app _ ≫ (TX.obj _).map c.hom =
    (RX.inverse.map a.hom ≫ RX.unitIso.inv.app _ ≫ q.hom) ≫
      P.map (tensorCoordinates S Y M L).hom ≫ m.hom ≫
        (TX.map b.inv).app (P.obj (RY.inverse.obj L.obj))
  rw [h, RX.inverse.map_comp, Category.assoc]
  erw [RX.unitInv_naturality_assoc t.hom]
  simp only [t, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc]
  exact congrArg
    (fun z ↦ RX.inverse.map a.hom ≫ RX.unitInv.app _ ≫ q.hom ≫
      P.map (tensorCoordinates S Y M L).hom ≫ m.hom ≫ z)
    (map_inverse_cancel (TX.obj (RX.inverse.obj ((S.finite.pull f).obj M).obj)) c
      ((TX.map b.inv).app (P.obj (RY.inverse.obj L.obj))))

end WeilConjectures.CompactSupportFiniteProjection
