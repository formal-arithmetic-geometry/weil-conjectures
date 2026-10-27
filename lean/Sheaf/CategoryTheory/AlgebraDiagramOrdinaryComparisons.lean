/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
import all Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence
import all Sheaf.CategoryTheory.FlatRestrictionOrdinaryComparisons
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso

/-! # Ordinary restriction and coefficient comparison

Source: Stacks 03EL (blueprint: lem-pur-algebra-diagram-ordinary-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}

private theorem inverseImageAcrossIso_smul
    (f : RingedPullback.{u, u, u, u, u} R S) [IsIso f.coefficient]
    (M : Modules.{u, u, u} R) (T : Sheaf K (Type u))
    (x : T ⟶ (sheafCompose K (forget CommRingCat.{u})).obj R)
    (y z : T ⟶ (underlying.{u, u, u} R).obj M)
    (h : ∀ (V : Cᵒᵖ) (v : T.obj.obj V),
      @id (M.val.obj V) (z.hom.app V v) =
        @id (R.obj.obj V) (x.hom.app V v) • @id (M.val.obj V) (y.hom.app V v))
    (U : Dᵒᵖ) (t : (f.uInv.obj T).obj.obj U) :
    (f.I.moduleUnderlying.inv.app M).hom.app U ((f.uInv.map z).hom.app U t) =
      ((inv f.coefficient).hom.app U (f.coefficient.hom.app U
        ((f.I.ringUnderlying.hom).hom.app U ((f.uInv.map x).hom.app U t)))) •
        (show (f.I.modules.obj M).val.obj U from
          (f.I.moduleUnderlying.inv.app M).hom.app U ((f.uInv.map y).hom.app U t)) := by
  have hi := f.I.moduleSMul M T x y z h U t
  have hc (v : f.RI.obj.obj U) :
      (inv f.coefficient).hom.app U (f.coefficient.hom.app U v) = v :=
    ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.hom.app U) (asIso f.coefficient).hom_inv_id) v
  exact hi.trans (congrArg (fun r : f.RI.obj.obj U ↦ r •
    (show (f.I.modules.obj M).val.obj U from
      (f.I.moduleUnderlying.inv.app M).hom.app U ((f.uInv.map y).hom.app U t)))
      (hc ((f.I.ringUnderlying.hom).hom.app U ((f.uInv.map x).hom.app U t)))).symm

private def inverseImageAcrossIso
    (f : RingedPullback.{u, u, u, u, u} R S) [IsIso f.coefficient] :
    SheafOfModules.AlgebraicInverseImage f.uInv R S := by
  let c := asIso f.coefficient
  let r := restrictionFunctor.{u, u, u, u} c.inv
  refine
    { ringUnderlying := f.I.ringUnderlying ≪≫
        (sheafCompose L (forget CommRingCat.{u})).mapIso c
      modules := f.I.modules ⋙ r
      moduleUnderlying := f.I.moduleUnderlying
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h U t
    exact (congrArg (c.hom.hom.app U) (f.I.ringAdd T x y z h U t)).trans
      ((c.hom.hom.app U).hom.map_add _ _)
  · intro T x y z h U t
    exact (congrArg (c.hom.hom.app U) (f.I.ringMul T x y z h U t)).trans
      ((c.hom.hom.app U).hom.map_mul _ _)
  · intro T x h U t
    exact (congrArg (c.hom.hom.app U) (f.I.ringZero T x h U t)).trans
      ((c.hom.hom.app U).hom.map_zero)
  · intro T x h U t
    exact (congrArg (c.hom.hom.app U) (f.I.ringOne T x h U t)).trans
      ((c.hom.hom.app U).hom.map_one)
  · intro M T x y z h U t
    exact f.I.moduleAdd M T x y z h U t
  · intro M T x h U t
    exact f.I.moduleZero M T x h U t
  · exact inverseImageAcrossIso_smul f

private theorem pullback_iso (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f) [IsIso f.coefficient] :
    ∃ e : f.L ≅ (inverseImageAcrossIso f).modules,
      ∀ M, k.q M ≫ (underlying.{u, u, u} S).map (e.hom.app M) = 𝟙 _ := by
  obtain ⟨t, ht₁, ht₂, ht⟩ := SheafOfModules.exists_scalarExtensionRingIso.{u, u, u, u}
    (asIso f.coefficient)
  let res := restrictionFunctor.{u, u, u, u} (inv f.coefficient)
  let e : f.L ≅ f.I.modules ⋙ res := NatIso.ofComponents
    (fun M ↦ eqToIso (f.hobj M) ≪≫ t (f.I.modules.obj M)) (by
      intro M N a
      change f.L.map a ≫ (eqToHom (f.hobj N) ≫ (t (f.I.modules.obj N)).hom) =
        (eqToHom (f.hobj M) ≫ (t (f.I.modules.obj M)).hom) ≫ res.map (f.I.modules.map a)
      rw [f.hmap]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (fun z ↦ eqToHom (f.hobj M) ≫ z)
        (ht (f.I.modules.obj M) (f.I.modules.obj N) (f.I.modules.map a)))
  refine ⟨e, ?_⟩
  intro M
  ext U x
  change (t (f.I.modules.obj M)).hom.val.app U
    ((eqToHom (f.hobj M)).val.app U ((k.q M).hom.app U x)) = x
  rw [k.q_one]
  change (t (f.I.modules.obj M)).hom.val.app U
    (((eqToHom (f.hobj M).symm) ≫ eqToHom (f.hobj M)).val.app U
      (extensionTmul.{u, u, u} f.coefficient (f.I.modules.obj M) U 1 x)) = x
  rw [eqToHom_trans]
  change (t (f.I.modules.obj M)).hom.val.app U
    (SheafOfModules.scalarExtensionRingIsoTmul.{u, u, u, u}
      f.coefficient (f.I.modules.obj M) U x 1) = x
  exact (ht₁ (f.I.modules.obj M) U x 1).trans
    (by simp only [map_one, one_smul])

private theorem restriction_iso_of_inverse_images
    (f : RingedPullback.{u, u, u, u, u} R S)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (A : SheafOfModules.AlgebraicInverseImage f.uInv R S)
    (B : SheafOfModules.AlgebraicInverseImage f.uInv d.R' d.S')
    (hc : A.ringUnderlying.hom ≫
      (sheafCompose L (forget CommRingCat.{u})).map d.targetMap =
      f.uInv.map ((sheafCompose K (forget CommRingCat.{u})).map d.sourceMap) ≫
        B.ringUnderlying.hom) :
    ∃ e : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ A.modules ≅
      B.modules ⋙ restrictionFunctor.{u, u, u, u} d.targetMap,
      ∀ M : Modules.{u, u, u} d.R',
        (underlying.{u, u, u} S).map (e.hom.app M) =
          A.moduleUnderlying.hom.app ((restrictionFunctor.{u, u, u, u} d.sourceMap).obj M) ≫
            B.moduleUnderlying.inv.app M := by
  let := f.finiteLimits
  have hex (M : Modules.{u, u, u} d.R') :=
    CategoryTheory.FlatRingedDiagramInput.inverse_change_hom A B d.sourceMap d.targetMap
      rfl (by simpa only [eqToHom_refl, Category.id_comp] using hc) M
  let h (M : Modules.{u, u, u} d.R') := (hex M).choose
  have hh (M : Modules.{u, u, u} d.R') :
      (underlying.{u, u, u} S).map (h M) =
        A.moduleUnderlying.hom.app ((restrictionFunctor.{u, u, u, u} d.sourceMap).obj M) ≫
          B.moduleUnderlying.inv.app M := by
    exact (hex M).choose_spec
  have hi (M : Modules.{u, u, u} d.R') : IsIso (h M) := by
    have : IsIso ((underlying.{u, u, u} S).map (h M)) := by rw [hh]; infer_instance
    exact isIso_of_reflects_iso _ (underlying.{u, u, u} S)
  let β : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ A.modules ⟶
      B.modules ⋙ restrictionFunctor.{u, u, u, u} d.targetMap :=
    { app := h
      naturality := by
        intro M N g
        apply (underlying.{u, u, u} S).map_injective
        rw [Functor.map_comp, Functor.map_comp, hh, hh]
        erw [← Category.assoc,
          A.moduleUnderlying.hom.naturality
            ((restrictionFunctor.{u, u, u, u} d.sourceMap).map g),
          Category.assoc, B.moduleUnderlying.inv.naturality g, Category.assoc]
        rfl }
  let e : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ A.modules ≅
      B.modules ⋙ restrictionFunctor.{u, u, u, u} d.targetMap :=
    NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (h M) (hi M))
    (fun g ↦ β.naturality g)
  exact ⟨e, hh⟩


/-- Restriction commutes with the geometric pullbacks, with its actual generator
normalization. Source: Stacks 03EL
(blueprint: lem-pur-algebra-diagram-ordinary-comparisons). -/
theorem ordinary_restriction
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [IsIso f.coefficient] [IsIso d.coefficient'] :
    ∃ e : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
      (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap,
      ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
        (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
        generator f k x ≫ (underlying.{u, u, u} S).map (e.hom.app H) =
          generator (changed f d) k' x := by
  have : IsIso (changed f d).coefficient := by dsimp [changed]; infer_instance
  obtain ⟨eY, heY⟩ := pullback_iso f k
  obtain ⟨eX, heX⟩ := pullback_iso (changed f d) k'
  let A := inverseImageAcrossIso f
  let B := inverseImageAcrossIso (changed f d)
  have hc : A.ringUnderlying.hom ≫
      (sheafCompose L (forget CommRingCat)).map d.targetMap =
      f.uInv.map ((sheafCompose K (forget CommRingCat)).map d.sourceMap) ≫
        B.ringUnderlying.hom := by
    change (f.I.ringUnderlying.hom ≫
      (sheafCompose L (forget CommRingCat)).map f.coefficient) ≫ _ =
      _ ≫ (d.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat)).map d.coefficient')
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← d.square, Functor.map_comp, ← Category.assoc,
      ← d.inverseImageMap_graph, Category.assoc]
  obtain ⟨b, hb⟩ := restriction_iso_of_inverse_images f d A B hc
  let e := Functor.isoWhiskerLeft (restrictionFunctor.{u, u, u, u} d.sourceMap) eY ≪≫ b ≪≫
    Functor.isoWhiskerRight eX.symm (restrictionFunctor.{u, u, u, u} d.targetMap)
  refine ⟨e, ?_⟩
  intro M Z x
  change generator f k x ≫ (underlying.{u, u, u} S).map
    (eY.hom.app _ ≫ b.hom.app M ≫
      (restrictionFunctor.{u, u, u, u} d.targetMap).map (eX.inv.app M)) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [generator]
  simp only [Category.assoc]
  erw [← Category.assoc (k.q ((restrictionFunctor d.sourceMap).obj M)),
    heY, Category.id_comp, hb]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  have hq : k'.q M = (underlying.{u, u, u} d.S').map (eX.inv.app M) := by
    apply (cancel_mono ((underlying.{u, u, u} d.S').map (eX.hom.app M))).1
    rw [heX, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rfl
  rw [hq]
  rfl

/-- The underlying coefficient module pulls back to the target coefficient
module, with the structural generator formula. Source: Stacks 03EL
(blueprint: lem-pur-algebra-diagram-ordinary-comparisons). -/
theorem coefficient_iso
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [IsIso f.coefficient] [IsIso d.coefficient'] :
    ∃ β : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap,
      ∀ (Z : Sheaf K (Type u))
        (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d.sourceMap)),
        generator f k x ≫ (underlying.{u, u, u} S).map β.hom =
          f.uInv.map x ≫ d.I'.ringUnderlying.hom ≫
            (sheafCompose L (forget CommRingCat.{u})).map d.coefficient' := by
  obtain ⟨e, he⟩ := ordinary_restriction f k d k'
  have : IsIso (changed f d).coefficient := by dsimp [changed]; infer_instance
  obtain ⟨eX, heX⟩ := pullback_iso (changed f d) k'
  let B := inverseImageAcrossIso (changed f d)
  let U := SheafOfModules.unit
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj d.R')
  obtain ⟨v, hv⟩ := SheafOfModules.inverseImage_unit_iso d.R' d.S' f.uInv B
  have hv' : (underlying.{u, u, u} d.S').map v.inv =
      B.moduleUnderlying.hom.app U ≫ B.ringUnderlying.hom := by
    apply (cancel_epi ((underlying.{u, u, u} d.S').map v.hom)).mp
    rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, hv]
    change 𝟙 _ = B.ringUnderlying.inv ≫
      B.moduleUnderlying.inv.app U ≫ B.moduleUnderlying.hom.app U ≫ B.ringUnderlying.hom
    simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  let β : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap :=
    e.app U ≪≫ (restrictionFunctor.{u, u, u, u} d.targetMap).mapIso
      (eX.app U ≪≫ v.symm)
  refine ⟨β, ?_⟩
  intro Z x
  change generator f k x ≫ (underlying.{u, u, u} S).map
    (e.hom.app U ≫ (restrictionFunctor.{u, u, u, u} d.targetMap).map
      (eX.hom.app U ≫ v.inv)) = _
  rw [Functor.map_comp, ← Category.assoc, he]
  change (f.uInv.map x ≫ d.I'.moduleUnderlying.inv.app U ≫ k'.q U) ≫
    (underlying.{u, u, u} d.S').map (eX.hom.app U ≫ v.inv) = _
  rw [Functor.map_comp, Category.assoc, Category.assoc,
    ← Category.assoc (k'.q U), heX, Category.id_comp, hv']
  change f.uInv.map x ≫ d.I'.moduleUnderlying.inv.app U ≫
    d.I'.moduleUnderlying.hom.app U ≫
      (d.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d.coefficient') = _
  rw [Iso.inv_hom_id_app_assoc]
end CategoryTheory.AlgebraDiagramPullback
