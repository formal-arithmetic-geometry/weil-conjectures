/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NB, P9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact

/-! # Adjunction-normalized composition with independent coefficient universes

Source: Stacks Project, sites-modules.tex, Tag 03D8,
lemma-push-pull-composition-modules
(blueprint: lem-pur-proetale-module-pullback-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t r
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private abbrev ringDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

private theorem constantSection_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).app W ≫
      (coefficientProEtaleDirectRingMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((ringDirectImage.{t,r} f).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun t ↦ t.app W) h

private noncomputable def sheafComp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y) :
    ringDirectImage.{t,r} b ⋙
      ringDirectImage.{t,r} a ≅
        ringDirectImage.{t,r} (b ≫ a) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).symm)
    CommRingCat.{max r (t + 1)} (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)

private theorem rho_comp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    coefficientProEtaleDirectRingMap a A ≫
      (ringDirectImage.{t,r} a).map
        (coefficientProEtaleDirectRingMap b A) ≫
          (sheafComp a b).hom.app
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A) =
            coefficientProEtaleDirectRingMap (b ≫ a) A := by
  apply (sheafificationAdjunction (ProEt.topology T) CommRingCat.{max r (t + 1)}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, ← Category.assoc, constantSection_unit]
  change ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange a).op.obj W) ≫
      (coefficientProEtaleDirectRingMap b A).hom.app
        ((proEtaleBaseChange a).op.obj W)) ≫
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
          W.unop).op =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj A)).app W ≫
        (coefficientProEtaleDirectRingMap (b ≫ a) A).hom.app W
  rw [constantSection_unit,
    constantSection_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
        W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

private def moduleRho {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max r (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
              ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)) :=
  ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap f A).hom
    (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})⟩

private theorem moduleRho_comp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
      (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
    moduleRho a A ≫
      ((proEtaleBaseChange a).sheafPushforwardContinuous RingCat.{max r (t + 1)}
        (ProEt.topology T) (ProEt.topology Y)).map (moduleRho b A) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom
        RingCat.{max r (t + 1)} (ProEt.topology T) (ProEt.topology X)).app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)) =
              moduleRho (b ≫ a) A := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  simp only [moduleRho]
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)}).map (h.hom.app W))
    (rho_comp a b A)

private noncomputable def directComp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    coefficientProEtaleModuleDirectImage b A ⋙ coefficientProEtaleModuleDirectImage a A ≅
      coefficientProEtaleModuleDirectImage (b ≫ a) A := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
    (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
  exact SheafOfModules.pushforwardComp (moduleRho a A) (moduleRho b A) ≪≫
    SheafOfModules.pushforwardNatIso _
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a) ≪≫
        SheafOfModules.pushforwardCongr (moduleRho_comp a b A)


/-- The unique left-adjoint compositor whose mate is restriction along canonical
fibre-product pasting, for any commutative constant ring in an independent universe.
Source: Stacks Project, Tag 03D8, lemma-push-pull-composition-modules
(blueprint: lem-pur-proetale-module-pullback-composition).
Proof: the fibre-product pasting isomorphism gives the displayed direct-image map
on sections. The constant-section coefficient maps commute with this pasting:
transpose through sheafification and both maps send each coefficient to its
constant section. This gives the module direct-image natural isomorphism d.
Conjugate d through the composite and single module adjunctions. The mate
bijection gives a and its uniqueness, without choosing an unrelated isomorphism.
This is the same construction as proEtaleConstantRingModulePullbackComposition,
using the independent-universe direct images and their specified adjunctions;
neither the site object and morphism universes nor the coefficient and scheme
universes are identified. -/
theorem coefficientModulePullbackComposition_existsUnique
    {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    ∃! a : coefficientProEtaleModulePullback (h ≫ f) A ≅
      coefficientProEtaleModulePullback f A ⋙ coefficientProEtaleModulePullback h A,
      ∃ d : coefficientProEtaleModuleDirectImage h A ⋙
          coefficientProEtaleModuleDirectImage f A ≅
            coefficientProEtaleModuleDirectImage (h ≫ f) A,
        conjugateIsoEquiv
          ((coefficientProEtaleModuleAdjunction f A).comp
            (coefficientProEtaleModuleAdjunction h A))
          (coefficientProEtaleModuleAdjunction (h ≫ f) A) a = d ∧
        ∀ (N : SheafOfModules.{max r (t + 1)}
            ((sheafCompose (ProEt.topology Z)
              (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
                ((constantSheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}).obj A)))
          (U : Y.ProEt)
          (x : ((coefficientProEtaleModuleDirectImage h A ⋙
            coefficientProEtaleModuleDirectImage f A).obj N).val.obj (op U)),
          (d.hom.app N).val.app (op U) x =
            N.val.map ((MorphismProperty.Over.pullbackComp h f).hom.app U).op x := by
  let d := directComp f h A
  let e := conjugateIsoEquiv
    ((coefficientProEtaleModuleAdjunction f A).comp
      (coefficientProEtaleModuleAdjunction h A))
    (coefficientProEtaleModuleAdjunction (h ≫ f) A)
  have hd : ∀ N U x, (d.hom.app N).val.app (op U) x =
      N.val.map ((MorphismProperty.Over.pullbackComp h f).hom.app U).op x := by
    intro N U x
    dsimp only [d, directComp]
    simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app]
    rfl
  refine ⟨e.symm d, ⟨d, e.apply_symm_apply d, hd⟩, ?_⟩
  rintro a ⟨d', ha, hd'⟩
  apply e.injective
  rw [e.apply_symm_apply, ha]
  apply Iso.ext
  ext N U x
  exact (hd' N U.unop x).trans (hd N U.unop x).symm

/-- Canonical composition fixed by the direct-image mate and the specified adjunction.
Source: Stacks Project, Tag 03D8
(blueprint: lem-pur-proetale-module-pullback-composition). -/
def coefficientModulePullbackComposition
    {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :=
  (coefficientModulePullbackComposition_existsUnique h f A).exists.choose

end AlgebraicGeometry.Scheme
