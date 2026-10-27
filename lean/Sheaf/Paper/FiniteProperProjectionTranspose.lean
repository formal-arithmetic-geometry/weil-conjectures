/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.Paper.FinitePartialPullbackTensor
import Sheaf.Paper.FiniteProperProjectionFixedRealization
import Sheaf.Paper.FiniteDirectCounitFixedRealization
import Sheaf.Paper.FinitePullbackTensorFixedCoordinates

/-! # The finite proper projection as a counit transpose

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

attribute [local irreducible] realization AlgebraicGeometry.ProEtale.derivedTensor

private theorem tensor_cancel_iso
    {A B T : Type*} [Category* A] [Category* B] [Category* T]
    (F : A ⥤ B ⥤ T) {V V' W : A} (e : V ≅ V')
    (g : V' ⟶ W) (h : V ⟶ W) (hc : e.hom ≫ g = h) (N : B) :
    (F.map e.inv).app N ≫ (F.map h).app N = (F.map g).app N := by
  rw [← hc, ← NatTrans.comp_app, ← F.map_comp]
  simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem counit_coordinate_calculation
    {C₀ D₀ C₁ D₁ : Type*} [Category* C₀] [Category* D₀]
    [Category* C₁] [Category* D₁]
    (U : D₀ ⥤ C₀) (R : C₀ ⥤ D₀) (JX : C₀ ⥤ C₁) (JY : D₀ ⥤ D₁)
    {P : D₁ ⥤ C₁} {Q : C₁ ⥤ D₁} (adj : P ⊣ Q)
    (p : U ⋙ JX ≅ JY ⋙ P) {A : D₀} {B : C₀} {V : D₁} {W : C₁}
    (r : A ⟶ R.obj B) (e : U.obj (R.obj B) ⟶ B)
    (d : JY.obj (R.obj B) ≅ Q.obj (JX.obj B))
    (a : JY.obj A ≅ V) (b : JX.obj B ≅ W) (v : V ⟶ Q.obj W)
    (hc : p.hom.app (R.obj B) ≫ P.map d.hom ≫ adj.counit.app (JX.obj B) = JX.map e)
    (hp : JY.map r ≫ d.hom ≫ Q.map b.hom = a.hom ≫ v) :
    JX.map (U.map r) ≫ JX.map e ≫ b.hom =
      p.hom.app A ≫ P.map a.hom ≫ P.map v ≫ adj.counit.app W := by
  rw [← hc]
  simp only [Category.assoc]
  rw [reassoc_of% (p.hom.naturality r)]
  have hε : P.map (Q.map b.hom) ≫ adj.counit.app W =
      adj.counit.app (JX.obj B) ≫ b.hom := adj.counit.naturality b.hom
  rw [← hε]
  have hmap := congrArg (fun t ↦ P.map t) hp
  simp only [Functor.map_comp] at hmap
  rw [reassoc_of% hmap]


set_option maxHeartbeats 800000 in
-- The explicit coefficient-coordinate composites require more than 200k elaboration heartbeats.
/-- The finite proper projection is the adjoint of pullback/tensor comparison followed
by counit tensor identity. The first input is arbitrary bounded constructible and
only the second input has finite Tor amplitude.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph, and
ConstructibleProjectionMates, properComponent
(blueprint: lem-sf-finite-proper-projection-transpose).
Proof: apply the faithful full constructible inclusion and then the inverse of the
specified coefficient realization. Expand properComponent as proper identification
inverse, compactification projection, and proper identification. The latter cancels
the identity-open compactification using finiteProperNormalization. The
remaining fixed-scalar proper projection has transpose equal to its canonical tensor
pullback comparison followed by its counit tensored with identity, by
Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit. The specified
finiteDirectAdjunctionNormalization identifies this counit with the supplied one.
Naturality moves the pullback and tensor realization maps across that counit. The
coefficient equivalence triangle identities cancel the two inner units. The resulting
pullback/tensor arrow is exactly pullbackTensorComparison above. Reflect the equation
through the faithful functors. The calculation uses no projection invertibility,
no Tor bound on the first input, and applies also to zero objects and empty schemes. -/
theorem properComponent_transpose (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (S.finite.pull f).map (properComponent S f K L) ≫
        (S.finite.pullDirectAdjunction f).counit.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L)) =
      (pullbackTensorComparison S f ((S.finite.direct f).obj K) L).hom ≫
        ((partialTensor S X).map
          ((S.finite.pullDirectAdjunction f).counit.app K)).app ((torPull S f).obj L) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let JX := coordinates (C := C) (E := E) (n := n) (hn := hn) X
  let JY := coordinates (C := C) (E := E) (n := n) (hn := hn) Y
  let P := fixedDerivedPull (C := C) (E := E) (n := n) f
  let Q := fixedDirect (C := C) (E := E) (n := n) f
  let adj := fixedAdjunction (C := C) (E := E) (n := n) f
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let N := (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj
  let phi := AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left
  let pi := AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left
  let A := ((partialTensor S Y).obj ((S.finite.direct f).obj K)).obj L
  let B := ((partialTensor S X).obj K).obj ((torPull S f).obj L)
  let a := directTensorCoordinates S f K L
  let b := targetCoordinates S f K L
  let p := pullCoordinatesIso S f
  have hc (W : sixFunctorFiniteCategory D C E n hn X) :
      p.hom.app ((S.finite.direct f).obj W) ≫ P.map (directCoordinates S f W).hom ≫
          adj.counit.app (JX.obj W) =
        JX.map ((S.finite.pullDirectAdjunction f).counit.app W) := by
    simpa only [p, pullCoordinatesIso_hom_app] using directCounit_fixed_realization S f W
  have hp : JY.map (properComponent S f K L) ≫ (directCoordinates S f B).hom ≫
      Q.map b.hom = a.hom ≫ (pi.app (JX.obj K)).app N :=
    properComponent_fixed_realization S f K L
  have hmu : JX.map (pullbackTensorComparison S f ((S.finite.direct f).obj K) L).hom ≫
      (targetCoordinates S f ((S.finite.pull f).obj ((S.finite.direct f).obj K)) L).hom =
    p.hom.app A ≫ P.map (tensorCoordinates S Y ((S.finite.direct f).obj K) L).hom ≫
      (phi.app (JY.obj ((S.finite.direct f).obj K))).app N ≫
      (TX.map (fixedPullRealization S f ((S.finite.direct f).obj K)).inv).app (P.obj N) := by
    simpa only [p, pullCoordinatesIso_hom_app] using
      pullbackTensor_fixed_coordinates S f ((S.finite.direct f).obj K) L
  apply JX.map_injective
  apply (cancel_mono b.hom).1
  simp only [Functor.map_comp, Category.assoc]
  have left : JX.map ((S.finite.pull f).map (properComponent S f K L)) ≫
      JX.map ((S.finite.pullDirectAdjunction f).counit.app B) ≫ b.hom =
    p.hom.app A ≫ P.map a.hom ≫
      (phi.app (Q.obj (JX.obj K))).app N ≫
      (TX.map (adj.counit.app (JX.obj K))).app (P.obj N) := by
    have hl := counit_coordinate_calculation (S.finite.pull f) (S.finite.direct f)
      JX JY adj p (properComponent S f K L)
      ((S.finite.pullDirectAdjunction f).counit.app B) (directCoordinates S f B)
      a b ((pi.app (JX.obj K)).app N) (hc B) hp
    refine hl.trans ?_
    exact congrArg (fun t ↦ p.hom.app A ≫ P.map a.hom ≫ t)
      (AlgebraicGeometry.ProEtale.map_rightDerivedLowerStarProjectionMap_comp_counit
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left (JX.obj K) N)
  erw [left]
  symm
  erw [targetCoordinates_naturality S f
    ((S.finite.pullDirectAdjunction f).counit.app K) L]
  erw [reassoc_of% hmu]
  have ht :
      (TX.map (fixedPullRealization S f ((S.finite.direct f).obj K)).inv).app (P.obj N) ≫
        (TX.map (JX.map ((S.finite.pullDirectAdjunction f).counit.app K))).app (P.obj N) =
      (TX.map (P.map (directCoordinates S f K).hom ≫ adj.counit.app (JX.obj K))).app
        (P.obj N) := by
    apply tensor_cancel_iso
    simpa only [p, pullCoordinatesIso_hom_app] using hc K
  erw [ht]
  simp only [TX.map_comp, NatTrans.comp_app]
  have hphi := NatTrans.congr_app (phi.naturality (directCoordinates S f K).hom) N
  change P.map ((TY.map (directCoordinates S f K).hom).app N) ≫
      (phi.app (Q.obj (JX.obj K))).app N =
    (phi.app (JY.obj ((S.finite.direct f).obj K))).app N ≫
      (TX.map (P.map (directCoordinates S f K).hom)).app (P.obj N) at hphi
  erw [← reassoc_of% hphi, ← P.map_comp_assoc]
  rfl

end WeilConjectures.CompactSupportFiniteProjection
