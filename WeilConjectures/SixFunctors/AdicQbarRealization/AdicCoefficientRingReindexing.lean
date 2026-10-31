/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicReindexingData
import all WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # The function-normalized native coefficient-ring reindexing

Source: Bhatt--Scholze, Sections 6.8.1--6.8.2 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

private theorem nativeRing_mul (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X) (W : X.ProEtᵒᵖ)
    (s t : (ring l X R).obj.obj W) :
    s * t = ULift.up (s.down * t.down) := by
  rw [CategoryTheory.ScalarForgetting.sectionRing_mul (ProEt.topology X)
    (ULift.{u + 1} (PadicAlgCl l)) (ProEtale.adicConstantSheaf l X) W s t]
  change ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l))
      (ProEtale.adicConstantSheaf l X) (ProEtale.adicConstantSheaf l X) ≫
    (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l)).map
      (MonObj.mul (X := ProEtale.adicConstantSheaf l X))).app W) _ = _
  rw [Sheaf.μ_comp_map_mul]
  exact ProEtale.adicConstantSheaf_mul_app_tmul X s t

private def normalizedRingReindex
    {X Y : Scheme.{u}} (g : X ≅ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) :
    RingReindex l X g.hom R S where
  iso := (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun W ↦ by
      let A : CommRingCat.{u + 1} :=
        ((isoSectionwiseInverseImage g.hom CommRingCat.{u + 1}).obj
          (ring l Y S)).obj.obj W
      let B : CommRingCat.{u + 1} := (ring l X R).obj.obj W
      let e : @RingEquiv A B A.commRing.toMul B.commRing.toMul
          A.commRing.toAdd B.commRing.toAdd :=
        { toEquiv := Equiv.refl _
          map_mul' := by
            intro x y
            exact (nativeRing_mul l Y S _ x y).trans
              (nativeRing_mul l X R W x y).symm
          map_add' := by intros; rfl }
      exact @RingEquiv.toCommRingCatIso A B A.commRing B.commRing e)
      (by intros; ext s; rfl))
  functions := by intros; rfl

/-- Sectionwise inverse image identifies the native coefficient rings by the same functions.
Source: BS 6.8.1--6.8.2 and Remark 6.8.15
(blueprint: lem-sf-adic-coefficient-ring-reindexing).

Proof: At each site object the two section types are the same ULift of the subalgebra
of locally finite continuous functions on the underlying scheme. The identity function
is additive. The section-ring multiplication formula and the native coefficient-ring
multiplication formula identify both multiplications with pointwise multiplication,
so the identity is a ring equivalence. Restriction maps are the same maps of functions,
which proves naturality. Full faithfulness of the sheaf-to-presheaf functor lifts the
sectionwise equivalence to a sheaf isomorphism. Its functions equation is reflexivity. -/
theorem exists_function_normalized_ring_reindex {X Y : Scheme.{u}} (g : X ≅ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) :
    Nonempty (RingReindex l X g.hom R S) :=
  ⟨normalizedRingReindex l g R S⟩

end WeilConjectures.AdicQbarRealization
