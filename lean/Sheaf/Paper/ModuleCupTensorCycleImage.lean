/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData

/-! # Evaluating one realized pairing in derived homology

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: new-module-cup-tensor-cycle-image)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

local instance cupTensorCycleCommRing : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

set_option maxHeartbeats 1000000 in
-- Comparing the two presentations of module sheaves requires extra instance reductions.
omit [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
/-- The section formula of a realized pairing sends the tensor of extended cycles
 to the extended output cycle.
Source: Stacks Project, Tag 0FKU, the tensor-of-cocycles calculation in Lemma 20.31.3.
(blueprint: new-module-cup-tensor-cycle-image)
Proof: apply the monomorphism given by the target cycle inclusion, then the global
sections map of extendXIso. Naturality of cycle inclusion identifies the image
with the degree p+q component of the composite. The tensor-summand formula for
nu and Realizes t turn this component into D.pair p q top a.val b.val. The three
extension equations and hc identify it with the target cycle. Cancel the extension
isomorphism and the cycle inclusion. This includes p=0 or q=0, zero cycles and zero
modules; no incoming differential or flatness assumption is used. -/
theorem moduleCup_tensor_cycle_image
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
        CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ :=
      S.mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ (ν : T.obj D.left.integerComplex ⊗ T.obj D.right.integerComplex ⟶
        T.obj (D.left.integerComplex ⊗ D.right.integerComplex)),
    (∀ (i j n : ℤ) (h : i + j = n) (x : Γ(D.left.integerComplex.X i, ⊤))
        (y : Γ(D.right.integerComplex.X j, ⊤)),
      (ν.f n).hom
          ((HomologicalComplex.ιTensorObj (T.obj D.left.integerComplex)
            (T.obj D.right.integerComplex) i j n h).hom
            (TensorProduct.tmul Γ(X, ⊤) x y)) =
        (HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          i j n h).val.app (op ⊤) (tmulSection x y)) →
    ∀ (za : (T.obj D.left.integerComplex).cycles (p : ℤ))
      (zb : (T.obj D.right.integerComplex).cycles (q : ℤ))
      (zc : (T.obj D.target.integerComplex).cycles ((p + q : ℕ) : ℤ)),
      S.map (D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).hom
        ((T.obj D.left.integerComplex).iCycles p za) = a.val →
      S.map (D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).hom
        ((T.obj D.right.integerComplex).iCycles q zb) = b.val →
      S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat rfl).hom
        ((T.obj D.target.integerComplex).iCycles (p + q : ℕ) zc) = c.val →
    ∀ z : (T.obj D.left.integerComplex ⊗ T.obj D.right.integerComplex).cycles
        ((p + q : ℕ) : ℤ),
      (T.obj D.left.integerComplex ⊗ T.obj D.right.integerComplex).iCycles
          (p + q : ℕ) z =
        (HomologicalComplex.ιTensorObj (T.obj D.left.integerComplex)
          (T.obj D.right.integerComplex) p q (p + q : ℕ) (by omega))
          (TensorProduct.tmul Γ(X, ⊤)
            ((T.obj D.left.integerComplex).iCycles p za)
            ((T.obj D.right.integerComplex).iCycles q zb)) →
      HomologicalComplex.cyclesMap (ν ≫ T.map t) (p + q : ℕ) z = zc := by
  intro S T ν hν za zb zc ha hb hcc z hz
  let n : ℤ := (p + q : ℕ)
  let f := ν ≫ T.map t
  apply (ModuleCat.mono_iff_injective ((T.obj D.target.integerComplex).iCycles n)).mp
    inferInstance
  apply (ModuleCat.mono_iff_injective
    (S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat rfl).hom)).mp inferInstance
  rw [hcc]
  have hi := congrArg (fun g ↦ g z) (HomologicalComplex.cyclesMap_i f n)
  simp only [ModuleCat.comp_apply] at hi
  rw [hi]
  change S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat rfl).hom
    ((S.map (t.f n)) ((ν.f n) ((T.obj D.left.integerComplex ⊗
      T.obj D.right.integerComplex).iCycles n z))) = c.val
  rw [hz]
  rw [hν]
  have hza : ((D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv).val.app
      (op ⊤) a.val = (T.obj D.left.integerComplex).iCycles p za := by
    have h := congrArg (fun x ↦
      S.map (D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv x) ha
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id] at h
    erw [CategoryTheory.Functor.map_id, ModuleCat.id_apply] at h
    exact h.symm
  have hzb : ((D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv).val.app
      (op ⊤) b.val = (T.obj D.right.integerComplex).iCycles q zb := by
    have h := congrArg (fun x ↦
      S.map (D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv x) hb
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id] at h
    erw [CategoryTheory.Functor.map_id, ModuleCat.id_apply] at h
    exact h.symm
  rw [hc]
  have h := ht p q ⊤ a.val b.val
  erw [hza, hzb] at h
  exact h

end
end AlgebraicGeometry.Scheme.Modules
