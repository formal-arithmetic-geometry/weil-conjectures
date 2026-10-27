/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Sheaf.CategoryTheory.Sites.OrientedProductLargeRepresentableComparison

/-! # Projections and orientation of the large triple site

Source: ILO Exposé XI §1.3.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v w e ve
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OrientedProduct

/-- The geometric morphism induced by a continuous finite-limit-preserving functor.
Source: Stacks Project Tag 00X6
(blueprint: lem-trf-large-oriented-projections). -/
noncomputable def largeSiteMorphism {C : Type w} [Category.{v} C]
    {T : Type (max v w)} [Category.{v} T] (J : GrothendieckTopology C)
    (L : GrothendieckTopology T) (H : C ⥤ T) [H.IsContinuous J L]
    [HasFiniteLimits C] [PreservesFiniteLimits H] :
    GeometricMorphism (Sheaf L (Type (max v w))) (Sheaf J (Type (max v w))) := by
  have : RepresentablyFlat H := flat_of_preservesFiniteLimits H
  have : AB5OfSize.{v, max w v} (Type (max v w)) :=
    AB5OfSize_shrink.{v, max w v, max w v, max w v} _
  exact
    { inverse := H.sheafPullback (Type (max v w)) J L
      direct := H.sheafPushforwardContinuous (Type (max v w)) J L
      adj := H.sheafAdjunctionContinuous (Type (max v w)) J L
      leftExact := inferInstance }

/-- The inverse image of an associated representable under the induced site morphism.
Source: Stacks Project Tag 00X6, Yoneda and uniqueness of left adjoints
(blueprint: lem-trf-large-oriented-projections). -/
noncomputable def largeAssociatedComparison {C : Type w} [Category.{v} C]
    {T : Type (max v w)} [Category.{v} T] (J : GrothendieckTopology C)
    (L : GrothendieckTopology T) (H : C ⥤ T) [H.IsContinuous J L]
    [HasFiniteLimits C] [PreservesFiniteLimits H] :
    largeAssociated J ⋙ (largeSiteMorphism J L H).inverse ≅ H ⋙ largeAssociated L := by
  let normalizeYoneda : uliftYoneda.{w} (C := C) ≅
      uliftYoneda.{max v w} (C := C) :=
    NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦
      { hom := ↾fun x ↦ ULift.up x.down
        inv := ↾fun x ↦ ULift.up x.down }))
  let adj₁ := (sheafificationAdjunction J (Type (max v w))).comp
    (H.sheafAdjunctionContinuous (Type (max v w)) J L)
  let adj₂ := (H.op.lanAdjunction (Type (max v w))).comp
    (sheafificationAdjunction L (Type (max v w)))
  let ε := Adjunction.leftAdjointUniq adj₁ adj₂
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft uliftYoneda ε ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight normalizeYoneda H.op.lan)
      (presheafToSheaf L (Type (max v w))) ≪≫
    Functor.isoWhiskerRight (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{w} H).symm
      (presheafToSheaf L (Type (max v w))) ≪≫ Functor.associator _ _ _

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]
  (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

private def middleFunctor : D ⥤ largeTriples F G where
  obj := largeMiddle F G
  map r := ⟨(F.map r, G.map r), r, by apply Prod.ext <;> simp [largeMiddle]⟩
  map_id _ := by ext <;> simp [largeMiddle]
  map_comp _ _ := by ext <;> simp [largeMiddle]

private noncomputable def middleToFirst : middleFunctor F G ⟶ F ⋙ largeFirst F G where
  app V := largeToFirst F G (largeMiddle F G V)
  naturality := by
    intro V W r
    apply CommaMorphism.ext
    · exact Prod.ext (by simp [middleFunctor, largeFirst, largeToFirst, largeMiddle])
        (terminalIsTerminal.hom_ext _ _)
    · exact terminalIsTerminal.hom_ext _ _

private noncomputable def middleToSecond : middleFunctor F G ⟶ G ⋙ largeSecond F G where
  app V := largeToSecond F G (largeMiddle F G V)
  naturality := by
    intro V W r
    apply CommaMorphism.ext
    · exact Prod.ext (terminalIsTerminal.hom_ext _ _)
        (by simp [middleFunctor, largeSecond, largeToSecond, largeMiddle])
    · exact terminalIsTerminal.hom_ext _ _

variable (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))

/-- The orientation associated with projection inverse-image formulas.

Source: ILO XI §1.3
(blueprint: lem-trf-large-oriented-projections).

Restriction along the type-(c) arrow from (FV,V,GV) to (FV,e,e) is bijective.
Its inverse followed by restriction from (e,e,GV) defines a transformation
on direct images, using Yoneda and the two projection adjunctions. Its naturality
in V and in the sheaf follows from the naturality of the structural arrows.
The formulas identifying f⁻¹(Vᵃ) and g⁻¹(Vᵃ) transport this transformation to
the stated composites. Taking adjoint mates gives the displayed formula on Vᵃ;
the associated representables generate the sheaf category, so they determine
this mate and hence the orientation uniquely.
-/
theorem largeOrientationExists
    (hc : ∀ V : D, IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map
      (largeToFirst F G (largeMiddle F G V)))) :
    ∃ τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct,
      LargeOrientationFormula F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ := by
  let A := largeAssociated (largeTopology J₁ J₂ F G)
  let r := Functor.whiskerRight (middleToFirst F G) A
  let s := Functor.whiskerRight (middleToSecond F G) A
  have : ∀ V, IsIso (r.app V) := hc
  have : IsIso r := NatIso.isIso_of_isIso_app _
  let φ : (F ⋙ largeFirst F G) ⋙ A ⟶ (G ⋙ largeSecond F G) ⋙ A :=
    (asIso r).inv ≫ s
  let ψ₁ : largeAssociated K.toGrothendieck ⋙ (p₁.comp f).inverse ≅
      (F ⋙ largeFirst F G) ⋙ A :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ηF p₁.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F π₁ ≪≫
      (Functor.associator _ _ _).symm
  let ψ₂ : largeAssociated K.toGrothendieck ⋙ (p₂.comp g).inverse ≅
      (G ⋙ largeSecond F G) ⋙ A :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ηG p₂.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G π₂ ≪≫
      (Functor.associator _ _ _).symm
  let δ := ψ₁.hom ≫ φ ≫ ψ₂.inv
  obtain ⟨τ, hτ, _⟩ :=
    largeDirectImageFromRepresentables K.toGrothendieck (p₂.comp g) (p₁.comp f) δ
  refine ⟨τ, ?_⟩
  intro V
  refine ⟨hc V, ?_⟩
  rw [hτ]
  simp [δ, ψ₁, ψ₂, φ, r, s, middleToFirst, middleToSecond, A,
    GeometricMorphism.comp, Category.assoc]

end CategoryTheory.OrientedProduct
