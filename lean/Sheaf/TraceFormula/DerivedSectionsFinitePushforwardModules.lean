/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.SixFunctors.Finite.GlobalSections
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import Sheaf.Paper.DerivedLerayComp
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Derived sections through finite pushforward for module sheaves

Source: Stacks Project, Étale Cohomology, Tag 03QP; Derived Categories, Tag 015M;
Sites, section-pullback (blueprint: lem-trf-derived-sections-finite-pushforward-modules).

The comparison is the published finite-pushforward Leray natural isomorphism.

## Main definitions and statement

* `finitePushforwardDerivedMate`: the canonical counit mate of the composition comparison.
* `finitePushforwardSectionsUnit`: the canonical comparison from termwise to derived sections.
* `derivedSectionsFinitePushforwardModules`: exactness, injectives, normalization on every
  bounded-below injective resolution, and compatibility with arbitrary pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical derived mate of the inverse-image composition comparison in a square
whose vertical maps are finite. No invertibility of the mate is assumed or used.

Source: Stacks Project, Sites, section-pullback; Étale Cohomology, Tag 03QP
(blueprint: lem-trf-derived-sections-finite-pushforward-modules). -/
noncomputable def finitePushforwardDerivedMate
    (Λ : Type (u + 1)) [CommRing Λ] {Z' Z Y' Y : Scheme.{u}}
    {g : Z' ⟶ Z} {p' : Z' ⟶ Y'} {p : Z ⟶ Y} {h : Y' ⟶ Y}
    [IsFinite p] [IsFinite p'] (sq : CommSq g p' p h) :
    (lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p').mapDerivedCategory :=
  (mateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryAdjunction
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p').mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryCompIso
          (upperStar (ModuleCat.{u + 1} Λ) h)
          (upperStar (ModuleCat.{u + 1} Λ) p')).symm ≪≫
        Functor.mapDerivedCategoryNatIso (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq) ≪≫
        Functor.mapDerivedCategoryCompIso
          (upperStar (ModuleCat.{u + 1} Λ) p)
          (upperStar (ModuleCat.{u + 1} Λ) g)).hom)).natTrans

/-- The canonical map from termwise sections to right-derived sections of a complex.
On a bounded-below complex of injectives it is an isomorphism, whose inverse computes
right-derived sections. This is the derived-functor unit transported from the homotopy
category, without making any choice of a resolution.

Source: Stacks Project, Derived Categories, Tag 015M
(blueprint: lem-trf-derived-sections-finite-pushforward-modules). -/
noncomputable def finitePushforwardSectionsUnit
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    DerivedCategory.Q.obj
        (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (DerivedCategory.Q.obj L) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app
      (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≫
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj L) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
      ((DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).hom.app L)

private theorem finiteSections_lowerStarCompGlobalSectionsIso_comp_comp
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((lowerStarComp (ModuleCat.{u + 1} Λ) f g (f ≫ g) rfl).hom.app P) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) (f ≫ g)).hom.app P =
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) g).hom.app
        (((f)_*[(ModuleCat.{u + 1} Λ)]).obj P) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f).hom.app P := by
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app P)).1
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [reassoc_of% ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) terminalIsTerminal).hom.naturality
    ((lowerStarComp (ModuleCat.{u + 1} Λ) f g (f ≫ g) rfl).hom.app P))]
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  congr 1
  change ((lowerStarComp (ModuleCat.{u + 1} Λ) f g (f ≫ g) rfl).hom.app P).hom.app
    (Opposite.op (⊤_ Z.Etale)) ≫ P.obj.map (PreservesTerminal.iso (f ≫ g).Etale).inv.op = _
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv, lowerStar_obj_val_map, ← Functor.map_comp, ← op_comp]
  congr 2
  exact ((terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj f.Etale).hom_ext _ _

private lemma finiteSections_generic_leray_composition
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (K : C ⥤ E) (J : D ⥤ B) (L : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] [J.Additive] [L.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes]
    [K.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ K) (a : G ⋙ H ≅ J) (b : F ⋙ J ≅ L) (c : K ⋙ H ≅ L)
    (h : ∀ T : HomotopyCategory C (.up ℤ),
      (H.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T) ≫
        (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app T =
      (NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        (NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app T) :
    Functor.whiskerRight (Functor.rightDerivedFunctorCompIso' F G e).hom
        H.rightDerivedFunctor ≫ (Functor.rightDerivedFunctorCompIso' K H c).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctor
          (Functor.rightDerivedFunctorCompIso' G H a).hom ≫
        (Functor.rightDerivedFunctorCompIso' F J b).hom := by
  let d := Functor.rightDerivedFunctorCompIso' F G e
  have : (F ⋙ G).PreservesKInjectiveComplexes := ⟨fun T _ => by
    change CochainComplex.IsKInjective
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    infer_instance⟩
  let i := Functor.isoWhiskerRight (Functor.rightDerivedFunctorCompIso F G)
    H.rightDerivedFunctor
  let α := Functor.rightDerivedFunctorCompUnit (F ⋙ G) H ≫
    Functor.whiskerLeft DerivedCategory.Qh i.hom
  have : ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) ⋙ H.rightDerivedFunctor
      ).IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Functor.isRightDerivedFunctor_iff_of_iso
      (Functor.rightDerivedFunctorCompUnit (F ⋙ G) H) α
      (HomotopyCategory.quasiIso _ (.up ℤ)) i rfl).mp inferInstance
  refine Functor.rightDerived_ext _ α (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext T : 2
  have hα : α.app T =
      H.rightDerivedFunctorUnit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj T)) ≫
        H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) := by
    dsimp only [α, i, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [comp_unit_app]
    erw [Category.assoc, ← Functor.map_comp]
    congr 2
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, hα, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp]
  have hfg := NatTrans.congr_app (comp_fac F G K e) T
  have hc := NatTrans.congr_app (comp_fac K H L c) T
  have ha := NatTrans.congr_app (comp_fac G H J a)
    ((F.mapHomotopyCategory (.up ℤ)).obj T)
  have hb := NatTrans.congr_app (comp_fac F J L b) T
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hfg hc ha hb
  rw [comp_unit_app] at hc ha hb
  have hn := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T)
  have hna := (Functor.rightDerivedFunctorCompIso' G H a).hom.naturality
    (F.rightDerivedFunctorUnit.app T)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hna
  change H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      H.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' K H c).hom.app (DerivedCategory.Qh.obj T) =
    H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      (Functor.rightDerivedFunctorCompIso' G H a).hom.app
        (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' F J b).hom.app (DerivedCategory.Qh.obj T)
  rw [← Functor.map_comp_assoc, hfg, Functor.map_comp]
  simp only [Category.assoc] at hc ha hb ⊢
  erw [← reassoc_of% hn]
  erw [hc]
  rw [comp_unit_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hna, reassoc_of% ha, hb]
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  exact h T

set_option maxHeartbeats 1000000 in
-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteSections_derived_leray_composition
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    Functor.whiskerRight (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g f).hom
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) (g ≫ f)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) f).hom ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) g).hom := by
  rw [derived_comp_eq (ModuleCat.{u + 1} Λ)]
  apply finiteSections_generic_leray_composition
  intro T
  obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
  have ht : ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (lowerStarComp (ModuleCat.{u + 1} Λ) g f).hom (.up ℤ)).app T) ≫
      (NatTrans.mapHomologicalComplex
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) (g ≫ f)).hom (.up ℤ)).app T =
    (NatTrans.mapHomologicalComplex
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f).hom (.up ℤ)).app
        (((lowerStar (ModuleCat.{u + 1} Λ) g).mapHomologicalComplex (.up ℤ)).obj T) ≫
      (NatTrans.mapHomologicalComplex
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) g).hom (.up ℤ)).app T := by
    ext n : 1
    exact finiteSections_lowerStarCompGlobalSectionsIso_comp_comp Λ g f (T.X n)
  have hq := (HomotopyCategory.quotient (ModuleCat.{u + 1} Λ) (.up ℤ)).congr_map ht
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_obj,
    Functor.mapHomotopyCategory_map, HomotopyCategory.quotient_obj_as,
    Functor.map_comp] using hq

private theorem finiteSections_derivedUnit_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ f)).unit.app K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) (g ≫ f)).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) g f) ≪≫
          Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
            (upperStar (ModuleCat.{u + 1} Λ) g)).hom.app K) =
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K)) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g f).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K)) := by
  simpa only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj] using
    (unit_conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ f))
      (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) g f) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
          (upperStar (ModuleCat.{u + 1} Λ) g)).hom K).symm

/-- The derived unit--Leray composites respect inverse-image composition.
Source: Stacks Project, Tags 015M and 03CB.
(blueprint: lem-weil-pbc-derived-unit-leray-comp).

Proof: Write U_f and U_g for the exact functors induced on derived categories, R_f and R_g for the
derived direct images, C:U_(g≫f)≅U_f followed by U_g for mapDerivedCategoryNatIso(upperStarComp)
followed by mapDerivedCategoryCompIso, and D:R_g followed by R_f≅R_(g≫f) for its conjugate. The
derived adjunction unit equation states eta_(g≫f),K followed by R_(g≫f)(C_K) equals eta_f,K
followed by R_f(eta_g,U_f(K)) followed by D_(U_g(U_f(K))). It is the unit-conjugation equation
for the adjunctions; the conjugate agrees with the canonical derived direct-image composition by
the right-derived comparison characterization.

The underived direct-image and terminal-section comparisons associate: evaluating an iterated
base change of the terminal object is the same as evaluating its composite base change, because
both isomorphisms commute with its projections. Deriving that equation yields RGamma_X(D_M)
followed by lambda_(g≫f),M equal to lambda_f,R_g(M) followed by lambda_g,M. Indeed both sides
precomposed with the composite right-derived unit are the localization of that underived
comparison. Direct image preserves K-injectives, so the composite right-derived functor has the
universal property, which makes these transformations equal.

Use naturality of lambda_(g≫f) at C_K to move RGamma_Z(C_K) across lambda_(g≫f). Substitute the
unit equation from step 1 and then the Leray composition equation from step 2, with
M=U_g(U_f(K)). The resulting composite contains RGamma_X(R_f(eta_g,U_f(K))) followed by
lambda_f,R_g(U_g(U_f(K))). Naturality of lambda_f at eta_g,U_f(K) replaces these by
lambda_f,U_f(K) followed by RGamma_Y(eta_g,U_f(K)). After reassociating, the result is exactly
the product of the unit-Leray composites for f at K and for g at U_f(K). -/
private theorem finiteSections_derivedUnitLeray_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ f)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) (g ≫ f)).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) (g ≫ f)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
      ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) g f) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
          (upperStar (ModuleCat.{u + 1} Λ) g)).hom.app K) =
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) f).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) g).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K)) := by
  let C := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) g f) ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
      (upperStar (ModuleCat.{u + 1} Λ) g)
  let U := (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory
  let V := (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
  let G := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  let H := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y
  let eta := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K
  let theta := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
    (U.obj K)
  let lambda := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    (ModuleCat.{u + 1} Λ) f).hom
  let mu := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    (ModuleCat.{u + 1} Λ) (g ≫ f)).hom
  have hn := mu.naturality (C.hom.app K)
  have hu := congrArg G.map (finiteSections_derivedUnit_comp Λ f g K)
  have hl := NatTrans.congr_app (finiteSections_derived_leray_composition Λ f g)
    (V.obj (U.obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hl
  have ht := lambda.naturality theta
  dsimp only [Functor.comp_map] at hn ht
  change G.map _ ≫ mu.app _ ≫ _ =
    G.map eta ≫ lambda.app (U.obj K) ≫ H.map theta ≫ _
  rw [← hn, ← G.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [hl]
  change G.map eta ≫ G.map (R.map theta) ≫ lambda.app _ ≫ _ = _
  erw [reassoc_of% ht]

private lemma finiteSections_generic_adjunction_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) (adjD : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hfac : ∀ T : HomotopyCategory C (.up ℤ),
      adjD.unit.app (DerivedCategory.Qh.obj T) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app T) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj T) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app T)) :
    adjD.unit = adj.mapDerivedCategoryRightDerivedAdjunction.unit ≫
      Functor.whiskerLeft L.mapDerivedCategory R.rightDerivedFunctorIsoMapDerivedCategory.hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
  intro T
  rw [← cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app T) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj T))]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [hfac]
  have hn := R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app T)
  rw [← reassoc_of% hn]
  have hu := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit T
  erw [reassoc_of% hu]
  have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj T)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  rw [reassoc_of% hf, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma finiteSections_adjunction_unit
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (p : X ⟶ Y) [IsFinite p]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryAdjunction.unit.app K =
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app K ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorIsoMapDerivedCategory.hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj K) := by
  exact congr_app (finiteSections_generic_adjunction_unit _ _
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryAdjunction
    (Adjunction.mapDerivedCategoryAdjunction_unit_app_fac _)) K

private noncomputable def finiteSections_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y ⟶
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (mapDerivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) f).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) f).hom

private lemma finiteSections_restriction_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (finiteSections_restriction Λ (g ≫ f)).app K ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) g f) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app K) =
    (finiteSections_restriction Λ f).app K ≫
      (finiteSections_restriction Λ g).app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K) := by
  simpa only [finiteSections_restriction, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, Category.assoc] using finiteSections_derivedUnitLeray_comp Λ f g K

private lemma finiteSections_restriction_comp'
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (hgf : gf = g ≫ f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (finiteSections_restriction Λ gf).app K ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
        ((Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} Λ) g f gf hgf) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app K) =
    (finiteSections_restriction Λ f).app K ≫
      (finiteSections_restriction Λ g).app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K) := by
  subst gf
  exact finiteSections_restriction_comp Λ f g K

set_option backward.isDefEq.respectTransparency false in
private lemma finiteSections_restriction_finite
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (p : X ⟶ Y) [IsFinite p]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (finiteSections_restriction Λ p).app K =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          p).mapDerivedCategoryAdjunction.unit.app K) ≫
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app _ := by
  rw [finiteSections_adjunction_unit]
  simp only [mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso,
    rightDerivedFunctorLowerStarIsoMapDerivedCategory, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, finiteSections_restriction,
    Functor.leftUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]
  have hc := (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).congr_map
    ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorIsoMapDerivedCategory.hom_inv_id_app
      ((upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj K))
  rw [Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [← Category.assoc _ _
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) p).hom.app _), hc]
  erw [Category.id_comp]

private lemma finiteSections_restriction_square
    (Λ : Type (u + 1)) [CommRing Λ] {Z' Z Y' Y : Scheme.{u}}
    {g : Z' ⟶ Z} {p' : Z' ⟶ Y'} {p : Z ⟶ Y} {h : Y' ⟶ Y}
    (sq : CommSq g p' p h)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (finiteSections_restriction Λ h).app K ≫
      (finiteSections_restriction Λ p').app
        ((upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory.obj K) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z').map
        ((Functor.mapDerivedCategorySquareIso
          (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq)).hom.app K) =
    (finiteSections_restriction Λ p).app K ≫
      (finiteSections_restriction Λ g).app
        ((upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj K) := by
  let C₁ := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} Λ) p' h (g ≫ p) sq.w) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let C₂ := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} Λ) g p) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have he : (Functor.mapDerivedCategorySquareIso
      (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq)).hom = C₁.inv ≫ C₂.hom := by
    simp only [Functor.mapDerivedCategorySquareIso, squareUpperStarIso, Iso.trans_hom,
      Iso.symm_hom, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, C₁, C₂, Iso.trans_inv,
      Category.assoc]
  rw [he]
  have h₁ := finiteSections_restriction_comp' Λ h p' (g ≫ p) sq.w K
  have h₂ := finiteSections_restriction_comp Λ p g K
  change (finiteSections_restriction Λ (g ≫ p)).app K ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z').map (C₁.hom.app K) = _ at h₁
  change (finiteSections_restriction Λ (g ≫ p)).app K ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z').map (C₂.hom.app K) = _ at h₂
  rw [← reassoc_of% h₁, NatTrans.comp_app, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using h₂

private lemma finiteSections_restriction_counit
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (p : X ⟶ Y) [IsFinite p]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (finiteSections_restriction Λ p).app
        ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj K) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          p).mapDerivedCategoryAdjunction.counit.app K) =
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app K := by
  rw [finiteSections_restriction_finite, Category.assoc, ← NatTrans.naturality]
  change _ ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
    ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.map _) ≫ _ = _
  rw [← Functor.map_comp_assoc, Adjunction.right_triangle_components]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

private lemma finiteSections_generic_leray_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H)
    (X : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app X) ≫
      G.rightDerivedFunctor.map
        (F.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj X) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) ≫
      H.rightDerivedFunctorUnit.app X := by
  have hf := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  have hc := NatTrans.congr_app (comp_fac F G H e) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [comp_unit_app] at hc
  rw [← G.rightDerivedFunctor.map_comp_assoc, ← hf]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simpa only [Category.assoc] using hc

private lemma finiteLeray_unit_h
    (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsFinite p]
    (X : HomotopyCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomotopyCategory (.up ℤ)).obj X) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
        ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryFactorsh.inv.app X) ≫
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
        (DerivedCategory.Qh.obj X) =
    DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p).hom (.up ℤ)).app X) ≫
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app X := by
  let F := lowerStar (ModuleCat.{u + 1} Λ) p
  let G := Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let H := Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  change G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app X) ≫
    (G.rightDerivedFunctor.map
      (F.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.rightDerivedFunctorCompIso' F G
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p)).hom.app
        (DerivedCategory.Qh.obj X)) = _
  exact finiteSections_generic_leray_unit F G H
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p) X

private noncomputable def finiteSections_generic_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (L : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj L) :=
  (DerivedCategory.quotientCompQhIso D).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj L) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app L)

private lemma finiteSections_generic_leray_complex
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H)
    (lam : F.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (hlam : ∀ X : HomotopyCategory C (.up ℤ),
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app X) ≫
        lam.hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) ≫
        H.rightDerivedFunctorUnit.app X)
    (L : CochainComplex C ℤ) :
    finiteSections_generic_unit G ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app L) ≫
      lam.hom.app (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app L) ≫
      finiteSections_generic_unit H L := by
  have h := hlam ((HomotopyCategory.quotient _ _).obj L)
  have hf : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj L) =
      F.mapDerivedCategoryFactors.hom.app L := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]
  have hfi : F.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ _).obj L) =
      F.mapDerivedCategoryFactors.inv.app L := by
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app L)).mp
    rw [← hf, Iso.inv_hom_id_app, hf, Iso.inv_hom_id_app]
    rfl
  rw [hfi] at h
  simp only [finiteSections_generic_unit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  exact h

private lemma finiteLeray_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsFinite p]
    (L : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    finitePushforwardSectionsUnit Λ Y
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
        ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryFactors.inv.app L) ≫
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
        (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p) (.up ℤ)).hom.app L) ≫
      finitePushforwardSectionsUnit Λ Z L := by
  have hh := finiteLeray_unit_h Λ p
  change ∀ X,
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
      (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomotopyCategory (.up ℤ)).obj X) ≫
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.map
      ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryFactorsh.inv.app X) ≫
    (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
      (DerivedCategory.Qh.obj X) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p).hom (.up ℤ)).app X) ≫
    (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app X at hh
  exact finiteSections_generic_leray_complex
    (lowerStar (ModuleCat.{u + 1} Λ) p)
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p)
    (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p)
    hh L

private lemma finiteSections_generic_normalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (e : F ⋙ G ≅ H)
    {M L : C} (i : M ⟶ L) [IsIso i] {T : E} {X : D}
    (eta : T ⟶ G.obj X) (alpha : X ⟶ F.obj L) :
    eta ≫ G.map (alpha ≫ F.map (inv i)) ≫ e.hom.app M ≫ H.map i =
      eta ≫ G.map alpha ≫ e.hom.app L := by
  have hn := e.hom.naturality i
  change G.map (F.map i) ≫ e.hom.app L = e.hom.app M ≫ H.map i at hn
  rw [G.map_comp]
  simp only [Category.assoc]
  have hc : G.map (F.map (inv i)) ≫ G.map (F.map i) = 𝟙 _ := by
    rw [← G.map_comp, ← F.map_comp, IsIso.inv_hom_id, F.map_id, G.map_id]
  rw [← hn, ← Category.assoc (G.map (F.map (inv i))), hc, Category.id_comp]

private lemma finiteSections_generic_square
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (P : B ⥤ A) (U : A ⥤ B) (V : B ⥤ D) (H : A ⥤ C)
    (P' : D ⥤ C) (U' : C ⥤ D)
    (GB : B ⥤ E) (GC : C ⥤ E) (GD : D ⥤ E) (GA : A ⥤ E)
    (rP : GA ⟶ U ⋙ GB) (rH : GA ⟶ H ⋙ GC)
    (rG : GB ⟶ V ⋙ GD) (rP' : GC ⟶ U' ⋙ GD)
    (lam : P ⋙ GA ⟶ GB) (lam' : P' ⋙ GC ⟶ GD)
    (eps : P ⋙ U ⟶ 𝟭 B) (eps' : P' ⋙ U' ⟶ 𝟭 D)
    (beta : P ⋙ H ⟶ V ⋙ P') (theta : H ⋙ U' ⟶ U ⋙ V)
    (hc : ∀ K, rP.app (P.obj K) ≫ GB.map (eps.app K) = lam.app K)
    (hc' : ∀ K, rP'.app (P'.obj K) ≫ GD.map (eps'.app K) = lam'.app K)
    (hs : ∀ K, rH.app K ≫ rP'.app (H.obj K) ≫ GD.map (theta.app K) =
      rP.app K ≫ rG.app (U.obj K))
    (hm : ∀ K, U'.map (beta.app K) ≫ eps'.app (V.obj K) =
      theta.app (P.obj K) ≫ V.map (eps.app K)) (K : B) :
    lam.app K ≫ rG.app K = rH.app (P.obj K) ≫ GC.map (beta.app K) ≫
      lam'.app (V.obj K) := by
  have hn := rG.naturality (eps.app K)
  change GB.map (eps.app K) ≫ rG.app K =
    rG.app (U.obj (P.obj K)) ≫ GD.map (V.map (eps.app K)) at hn
  have hn' := rP'.naturality (beta.app K)
  change GC.map (beta.app K) ≫ rP'.app (P'.obj (V.obj K)) =
    rP'.app (H.obj (P.obj K)) ≫ GD.map (U'.map (beta.app K)) at hn'
  rw [← hc K, Category.assoc, hn, ← Category.assoc, ← hs (P.obj K)]
  simp only [Category.assoc]
  rw [← GD.map_comp, ← hm K, GD.map_comp, ← reassoc_of% hn', hc' (V.obj K)]

/-- Finite direct image is exact, preserves injectives, and its canonical Leray comparison
commutes with the canonical restriction and base-change mate.

Source: Stacks Project, Étale Cohomology, Tag 03QP; Derived Categories, Tag 015M
(blueprint: lem-trf-derived-sections-finite-pushforward-modules).

Proof.

1. Finite direct image is exact for module coefficients by the generic finite-direct-image
instances. Its exact left adjoint implies preservation of injectives. A bounded-below
termwise-injective complex is K-injective, and so is its direct image. The two sections
units are therefore invertible.

2. The defining right-derived composition comparison satisfies its unit factorization.
Transport this identity from homotopy categories to complexes to obtain finite Leray
normalization. Naturality and cancellation of the localized resolution quasi-isomorphism
then give the displayed equation for every resolution, without choosing one.

3. The ordinary direct-image composition and terminal-section identifications associate:
both terminal-object maps are equal by terminality. Right-derived extensionality transports
this equality to the unbounded Leray comparisons. Conjugacy identifies the derived
composition comparison with the one specified by the exact inverse-image adjunctions.
Their unit equation proves composition of the unit--Leray restriction transformations.

4. Descending the two ordinary inverse-image composition comparisons gives the square
comparison used in the definition of finitePushforwardDerivedMate. Composition of
restriction therefore gives the corresponding restriction-square identity.

5. The canonical exact derived adjunction has the unit of the exact-left/right-derived
adjunction transported along the finite direct-image comparison. Their unit factorization
proves this equality of units. Its triangle identity says that restriction along a finite map,
followed by sections of the counit, equals the published finite Leray comparison.

6. Rewrite the right side of the desired square using this counit description for p'.
Naturality moves the mate through restriction along p'. The mate's counit formula replaces
it by the inverse-image square followed by pullback of the p-counit. The restriction-square
identity and naturality of restriction along g then identify the result with finite Leray
for p followed by restriction along g. No invertibility of the mate is used.
-/
theorem derivedSectionsFinitePushforwardModules
    (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsFinite p]
    (M : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [M.IsStrictlyGE a] :
    PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} Λ) p) ∧
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) p) ∧
    (lowerStar (ModuleCat.{u + 1} Λ) p).PreservesInjectiveObjects ∧
    (∀ (L : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (b : ℤ) [L.IsStrictlyGE b] [∀ n : ℤ, Injective (L.X n)]
      (i : M ⟶ L) [QuasiIso i],
      QuasiIso (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i) ∧
      CochainComplex.IsStrictlyGE
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) b ∧
      (∀ n : ℤ, Injective ((lowerStar (ModuleCat.{u + 1} Λ) p).obj (L.X n))) ∧
      IsIso (finitePushforwardSectionsUnit Λ Z L) ∧
      IsIso (finitePushforwardSectionsUnit Λ Y
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) ∧
      finitePushforwardSectionsUnit Λ Y
          (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
          ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryFactors.inv.app L ≫
            (lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.map
              (inv (DerivedCategory.Q.map i))) ≫
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
          (DerivedCategory.Q.obj M) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
          (DerivedCategory.Q.map i) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p)
            (ComplexShape.up ℤ)).hom.app L) ≫
        finitePushforwardSectionsUnit Λ Z L) ∧
    ∀ (Y' : Scheme.{u}) (h : Y' ⟶ Y),
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
          (DerivedCategory.Q.obj M) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (pullback.snd h p)).unit.app (DerivedCategory.Q.obj M)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (pullback.snd h p)).hom.app _ =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
            ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj
              (DerivedCategory.Q.obj M))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) h).hom.app _ ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
          ((finitePushforwardDerivedMate Λ
            (⟨pullback.condition.symm⟩ :
              CommSq (pullback.snd h p) (pullback.fst h p) p h)).app
              (DerivedCategory.Q.obj M)) ≫
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso
          Λ (pullback.fst h p)).hom.app _ := by
  let := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    |>.preservesInjectiveObjects_of_preservesFiniteLimits
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro L b hb hL i hi
    let : L.IsKInjective := CochainComplex.isKInjective_of_injective L b
    let : ∀ n : ℤ,
        Injective ((((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).X n) :=
      fun n ↦ (lowerStar (ModuleCat.{u + 1} Λ) p).injective_obj (L.X n)
    let : CochainComplex.IsKInjective (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) :=
      CochainComplex.isKInjective_of_injective _ b
    refine ⟨inferInstance, inferInstance, fun n ↦ inferInstance, ?_, ?_, ?_⟩
    · unfold finitePushforwardSectionsUnit
      infer_instance
    · unfold finitePushforwardSectionsUnit
      infer_instance
    · rw [finiteSections_generic_normalization
        (lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y)
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z)
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p)
        (DerivedCategory.Q.map i)]
      exact finiteLeray_unit Λ p L
  · intro Y' h
    let A := ModuleCat.{u + 1} Λ
    let g := pullback.snd h p
    let p' := pullback.fst h p
    let sq : CommSq g p' p h := ⟨pullback.condition.symm⟩
    let K := DerivedCategory.Q.obj M
    let P := (lowerStar A p).mapDerivedCategory
    let U := (upperStar A p).mapDerivedCategory
    let V := (upperStar A g).mapDerivedCategory
    let H := (upperStar A h).mapDerivedCategory
    let P' := (lowerStar A p').mapDerivedCategory
    let U' := (upperStar A p').mapDerivedCategory
    let ΓZ := rightDerivedGlobalSections A Z
    let ΓZ' := rightDerivedGlobalSections A (pullback h p)
    let ΓY' := rightDerivedGlobalSections A Y'
    have hh :=
      (finiteSections_generic_square P U V H P' U' ΓZ ΓY' ΓZ'
      (rightDerivedGlobalSections A Y)
      (finiteSections_restriction Λ p) (finiteSections_restriction Λ h)
      (finiteSections_restriction Λ g) (finiteSections_restriction Λ p')
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p').hom
      (upperStarLowerStarAdjunction A p).mapDerivedCategoryAdjunction.counit
      (upperStarLowerStarAdjunction A p').mapDerivedCategoryAdjunction.counit
      (finitePushforwardDerivedMate Λ sq)
      (Functor.mapDerivedCategorySquareIso (squareUpperStarIso A sq)).hom
      (finiteSections_restriction_counit Λ p) (finiteSections_restriction_counit Λ p')
      (finiteSections_restriction_square Λ sq) (fun T ↦ mateEquiv_counit _ _ _ T) K)
    simp only [finiteSections_restriction, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Category.id_comp, Category.assoc] at hh
    repeat erw [Category.id_comp] at hh
    exact hh

end AlgebraicGeometry.Etale
