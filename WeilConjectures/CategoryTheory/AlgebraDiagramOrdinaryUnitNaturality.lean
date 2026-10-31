/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
import all WeilConjectures.CategoryTheory.AlgebraDiagramOrdinaryComparisons
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Units and naturality of ordinary coefficient comparisons

Source: Stacks 03EL (blueprint: lem-pur-algebra-diagram-ordinary-unit-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

/-- The generator-normalized restriction and scalar-association maps carry the
source scalar unit to the target unit, by the defining scalar-association formula.
Source: Stacks 03EL
(blueprint: lem-pur-algebra-diagram-ordinary-unit-naturality). -/
theorem ordinary_unit_square
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [IsIso f.coefficient]
    (b : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
      (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap)
    (hb : ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
      generator f k x ≫ (underlying.{u, u, u} S).map (b.hom.app H) =
        generator (changed f d) k' x)
    (M : Modules.{u, u, u} R) :
    f.L.map ((extensionAdjunction d.sourceMap).unit.app M) ≫
      b.hom.app ((extensionFunctor d.sourceMap).obj M) ≫
      (restrictionFunctor d.targetMap).map ((scalarAssociation f k d k').hom.app M) =
        (extensionAdjunction d.targetMap).unit.app (f.L.obj M) := by
  obtain ⟨e, he⟩ := pullback_iso f k
  have hi : IsIso (generator f k (M := M) (𝟙 _)) := by
    have hq : k.q M = (underlying.{u, u, u} S).map (e.inv.app M) := by
      apply (cancel_mono ((underlying.{u, u, u} S).map (e.hom.app M))).1
      rw [he, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
      rfl
    dsimp [generator]
    rw [hq]
    infer_instance
  apply (underlying.{u, u, u} S).map_injective
  apply (cancel_epi (generator f k (M := M) (𝟙 _))).mp
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← generator_naturality f k ((extensionAdjunction d.sourceMap).unit.app M),
    Category.id_comp, hb]
  exact (Classical.choose_spec (scalarAssociation_existsUnique f k d k')).1 M
    ((underlying.{u, u, u} R).obj M) (𝟙 _)
/-- Compatible coefficient ring maps give the actual coefficient module square.
Cancel the invertible inverse-image generator and use the two generator formulas.
Source: Stacks 03EL
(blueprint: lem-pur-algebra-diagram-ordinary-unit-naturality). -/
theorem coefficient_naturality
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    [IsIso f.coefficient]
    (d d' : CoefficientSquare.{u, u, u, u, u} f)
    (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
    (beta' : f.L.obj (coefficient d'.sourceMap) ≅ coefficient d'.targetMap)
    (hb : ∀ (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d.sourceMap)),
      generator f k x ≫ (underlying.{u, u, u} S).map beta.hom =
        f.uInv.map x ≫ d.I'.ringUnderlying.hom ≫
          (sheafCompose L (forget CommRingCat.{u})).map d.coefficient')
    (hb' : ∀ (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d'.sourceMap)),
      generator f k x ≫ (underlying.{u, u, u} S).map beta'.hom =
        f.uInv.map x ≫ d'.I'.ringUnderlying.hom ≫
          (sheafCompose L (forget CommRingCat.{u})).map d'.coefficient')
    (psiY : d.R' ⟶ d'.R') (psiX : d.S' ⟶ d'.S')
    (hc : f.uInv.map ((sheafCompose K (forget CommRingCat.{u})).map psiY) ≫
      d'.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d'.coefficient' =
      d.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d.coefficient' ≫
        (sheafCompose L (forget CommRingCat.{u})).map psiX)
    (hY : coefficient d.sourceMap ⟶ coefficient d'.sourceMap)
    (hX : coefficient d.targetMap ⟶ coefficient d'.targetMap)
    (hy : ∀ (V : Cᵒᵖ) (b : d.R'.obj.obj V), hY.val.app V b = psiY.hom.app V b)
    (hx : ∀ (V : Dᵒᵖ) (b : d.S'.obj.obj V), hX.val.app V b = psiX.hom.app V b) :
    f.L.map hY ≫ beta'.hom = beta.hom ≫ hX := by
  obtain ⟨e, he⟩ := pullback_iso f k
  have hi (M : Modules.{u, u, u} R) : IsIso (k.q M) := by
    have h : k.q M = (underlying.{u, u, u} S).map (e.inv.app M) := by
      apply (cancel_mono ((underlying.{u, u, u} S).map (e.hom.app M))).1
      rw [he, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
      rfl
    rw [h]
    infer_instance
  have hgen : IsIso (generator f k (M := coefficient d.sourceMap) (𝟙 _)) := by
    dsimp [generator]
    infer_instance
  have hY' : (underlying.{u, u, u} R).map hY =
      (sheafCompose K (forget CommRingCat.{u})).map psiY := by
    ext V b
    exact hy V b
  have hX' : (underlying.{u, u, u} S).map hX =
      (sheafCompose L (forget CommRingCat.{u})).map psiX := by
    ext V b
    exact hx V b
  apply (underlying.{u, u, u} S).map_injective
  apply (cancel_epi (generator f k (M := coefficient d.sourceMap) (𝟙 _))).mp
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← generator_naturality f k hY, Category.id_comp, hb', hb]
  simpa only [hY', hX', Functor.map_id, Category.id_comp, Category.assoc] using hc

end CategoryTheory.AlgebraDiagramPullback
