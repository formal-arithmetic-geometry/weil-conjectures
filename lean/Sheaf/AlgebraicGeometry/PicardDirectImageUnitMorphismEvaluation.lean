/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphism
import Sheaf.AlgebraicGeometry.PicardAdjunctionSectionEvaluation

/-! # Evaluation of the canonical unit morphism

Source: Stacks Project, Tag 08HY; adjunction and naturality on opens.
(blueprint: lem-sc-picard-direct-image-unit-morphism-evaluation)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Evaluation of the unit morphism gives exactly the previously fixed section map.
Source: Stacks Project, Tag 08HY; adjunction and naturality on opens.
(blueprint: lem-sc-picard-direct-image-unit-morphism-evaluation)
Proof: Transposing back cancels the ordinary adjunction Hom equivalence and the
invertible pullback comparison on the structure sheaf. Evaluation at 1 and
naturality for the inclusion of top into the inverse image of top give the
restriction used in the definition of the section map. -/
theorem picardDirectImageUnitMorphism_evaluation
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (picardDirectImageUnitMorphism f L W k t ξ).val.app (Opposite.op ⊤)
        (1 : Γ(pullback f (t ≫ k), ⊤)) = picardDirectImageSectionMap f L W k t ξ := by
  let p := pullback.snd f (t ≫ k)
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  have h := picardAdjunctionSectionEvaluation p (Modules.pullback p)
    (Modules.pullbackPushforwardAdjunction p) e
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom) _ (picardDirectImageUnitMorphism f L W k t ξ)
  dsimp only [e, asIso_hom, picardDirectImageUnitMorphism, p, id_eq] at h
  simp only [IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply] at h
  exact h.symm


end AlgebraicGeometry.Scheme
