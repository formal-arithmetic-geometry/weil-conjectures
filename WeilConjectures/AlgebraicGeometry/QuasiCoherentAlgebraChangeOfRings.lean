/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorRelationPresentation
import WeilConjectures.AlgebraicGeometry.TensorRelationSectionQuotient

/-! # Change of rings between quasi-coherent algebras

The quasi-coherent `𝒪_Y`-algebras are the shared form `B C : Y.CommAlgebraSheaf`
(`= Under Y.sheaf`, def-weil-pbc-comm-algebra-sheaf) with `B.toModule.IsQuasicoherent`;
`φ : B ⟶ C` in `Under Y.sheaf` is a morphism of `𝒪_Y`-algebras, so `C.hom = B.hom ≫ φ.right`.
`B`-modules are `SheafOfModules` over `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj B.right`
and their underlying `𝒪_Y`-modules are obtained by scalar restriction along `B.hom`. Change of
rings uses the recorded sheafification construction, whose section tensor products
have the scalar factor first (`C(W) ⊗[B(W)] P(W)`). This is the usual tensor product
`P(W) ⊗[B(W)] C(W)` under the canonical symmetry, with the same sheafification map.

## References

* Stacks Project, Morphisms, proof of Lemma 01SB; Schemes, Lemma 01I8 (1) and Section 01LA.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

private theorem tensor_bijective_of_tmul
    {R M N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [AddCommMonoid P] [AddCommMonoid Q]
    (f : TensorProduct R M N →+ P) (e : P ≃+ Q) (l : TensorProduct R M N ≃+ Q)
    (h : ∀ m n, e (f (TensorProduct.tmul R m n)) = l (TensorProduct.tmul R m n)) :
    Function.Bijective f := by
  have hcomp : ∀ z, e (f z) = l z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact h m n
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (e.bijective.of_comp_iff' f).1
  simpa only [Function.comp_def, hcomp] using l.bijective

set_option backward.isDefEq.respectTransparency false in
/-- Change of rings between quasi-coherent algebras preserves quasi-coherence of the
underlying structure-sheaf module, and the sheafification map is bijective on affine opens. -/
theorem quasiCoherent_algebra_changeOfRings (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (hB : B.toModule.IsQuasicoherent) (hC : C.toModule.IsQuasicoherent)
    (hP : ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P).IsQuasicoherent) :
    ((SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)).IsQuasicoherent ∧
    ∀ (W : Y.Opens), IsAffineOpen W →
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W)) := by
  classical
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let S := tensorObj C.toModule P₀
  -- Reuse the colimit instances in these hypotheses when registering quasi-coherence.
  have := hB
  have := hC
  have := hP
  have hS := quasiCoherent_tensor_product_affine_sections C.toModule P₀
  have := hS.1
  have hF := quasiCoherent_tensor_product_affine_sections B.toModule S
  have := hF.1
  obtain ⟨δ, e, hrel, he⟩ := changeOfRings_tensor_relation_presentation Y B C φ P
  have hδ := quasiCoherent_cokernel_image δ
  have hqc := hδ.2.2.2.2.2.2.1
  refine ⟨(SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm hqc, ?_⟩
  intro W hW
  have hsections := hδ.2.2.2.2.2.2.2.2 ⟨W, hW⟩
  obtain ⟨l, hl⟩ := tensor_relation_section_quotient Y B C φ P δ W
    (hrel W) (hS.2 W hW) (hF.2 W hW) hsections.2.1 hsections.2.2.1
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W)
  let : Module (B.right.obj.obj (op W)) (C.right.obj.obj (op W)) :=
    Module.compHom _ (φ.right.hom.app (op W)).hom
  exact tensor_bijective_of_tmul (R := B.right.obj.obj (op W))
    η.hom.toAddMonoidHom (appLinearEquivOfIso e W).toAddEquiv l
    (fun c p ↦ (he W c p).trans (hl c p).symm)

end AlgebraicGeometry.Scheme.Modules
