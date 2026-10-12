/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Compatible pasted tensor-pullback adjunction

Source: Stacks Project, Cohomology, Tags 079W, 0D5S, and 0D5T.
(blueprint: lem-pc-ringed-space-pasted-pullback-adjunction).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem tensorPullback_preserves_kFlat
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
      K.IsKFlat → CochainComplex.IsKFlat (R := X.sheaf)
        ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
  intro K hK
  let e : (P.mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.tensorPullbackComplex g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩ K :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (h (K.X i))) (by
      intro i j hij
      change eqToHom (h (K.X i)) ≫ _ = P.map (K.d i j) ≫ eqToHom (h (K.X j))
      rw [hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rfl)
  have ht := CochainComplex.isKFlat_pullback g.hom.base X.sheaf Y.sheaf
    ⟨g.hom.c⟩ K hK
  let := SheafOfModules.monoidalCategory X.sheaf
  intro F hF i
  exact (ht F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e.symm)

private theorem compatible_single_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    [P.Additive] (adj : P ⊣ moduleDirectImage f)
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ)))
    (habs : ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
      (L ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α H)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))) :
    ∃ adj' : L ⊣ derivedModuleDirectImage f,
      ∀ K, adj'.unit.app (DerivedCategory.Qh.obj K) ≫
        (derivedModuleDirectImage f).map (α.app K) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (moduleDirectImage f).rightDerivedFunctorUnit.app
            ((P.mapHomotopyCategory (.up ℤ)).obj K) := by
  have := hL
  have := habs (derivedModuleDirectImage f)
  have : (derivedModuleDirectImage f ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit L ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X)) (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism
      (SheafOfModules.{u} (moduleRings X)))
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives _)
          |>.isIso_of_isRightDerivedFunctor _ I) L
  let a := adj.mapHomotopyCategory (.up ℤ)
  refine ⟨a.derived
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X)) (.up ℤ))
    α (moduleDirectImage f).rightDerivedFunctorUnit, ?_⟩
  intro K
  exact a.derivedη_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))
    α (moduleDirectImage f).rightDerivedFunctorUnit K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Elaborating the pasted comparison and unit uses several large sheaf-category instances.
/-- Successive tensor pullbacks and their derived functors have compatible
adjunctions; the left comparison is invertible on K-flat complexes.
Source: Stacks Project, Cohomology, lemma-adjoint (079W),
lemma-derived-pullback-composition (0D5S), and
lemma-derived-pushforward-composition (0D5T).
(blueprint: lem-pc-ringed-space-pasted-pullback-adjunction).

Proof: choose the concrete tensor module pullbacks P_g and P_f, with the
underived adjunctions induced by inverse image and extension of scalars.
On homotopy categories set G = P_g ⋙ P_f. Its right adjoint is f_* ⋙ g_*.
Choose the absolute left derived tensor pullbacks L_g and L_f computed on
K-flat complexes. Set L = L_g ⋙ L_f and derive each underived adjunction
using the right-derived units already specified in the statement. Compose
the resulting adjunctions. The left comparison at T is L_f(α_g(T)), followed
by α_f(P_g T), with the functor associators. For a K-flat K, α_g(K) is invertible;
P_g K is K-flat by pullback preservation, so α_f(P_g K) is invertible as well.
Thus α(K) is invertible. To check the unit equation, write η'_g, η'_f for
the two derived adjunction units and η_g, η_f for their underived units.
The composite unit is η'_g(QT) followed by Rg_*(η'_f(L_g QT)). Expand R(α(T))
and use naturality of η'_f at α_g(T). The inner composition becomes
α_g(T) followed by η'_f(Q(P_g T)) and Rf_*(α_f(P_g T)). Apply
Adjunction.derivedη_fac_app for f to the last two factors, and for g to
η'_g(QT) followed by Rg_*(α_g(T)). The result is Q(η_g(T)), β_g(P_g T),
Rg_*(Q(η_f(P_g T))), and Rg_*(β_f(P_f P_g T)), in that order.
Naturality of β_g at η_f(P_g T) moves the middle factors to
Q(g_*(η_f(P_g T))) followed by β_g(f_*P_f P_g T).
Combining the two Q-maps gives the underived composite adjunction unit;
the remaining factors are precisely β at G(T). This constructs the compatible
adjunction, rather than choosing an arbitrary adjunction of the same functors.
No direct image is assumed to preserve K-injectivity. -/
theorem exists_pasted_tensorPullback_adjunction
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    let F := (moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)
    let R := derivedModuleDirectImage f ⋙ derivedModuleDirectImage g
    let β : F ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R :=
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
          (moduleDirectImage g).rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit
          (derivedModuleDirectImage g) ≫ (Functor.associator _ _ _).hom
    ∃ (G : HomotopyCategory (SheafOfModules.{u} (moduleRings Z)) (ComplexShape.up ℤ) ⥤
        HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ))
      (adj : G ⊣ F)
      (L : DerivedCategory (SheafOfModules.{u} (moduleRings Z)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (adj' : L ⊣ R)
      (α : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh),
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ,
        K.IsKFlat → IsIso
          (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
      ∀ K, adj'.unit.app (DerivedCategory.Qh.obj K) ≫ R.map (α.app K) =
        DerivedCategory.Qh.map (adj.unit.app K) ≫ β.app (G.obj K) := by
  obtain ⟨Pf, hf, hfm, haf, ⟨af⟩⟩ := exists_tensorModulePullback f
  obtain ⟨Pg, hg, hgm, hag, ⟨ag⟩⟩ := exists_tensorModulePullback g
  have := haf
  have := hag
  obtain ⟨Lf, αf, hLf, hKf, habsf⟩ :=
    exists_absolute_leftDerived_tensorModulePullback f Pf hf hfm
  obtain ⟨Lg, αg, hLg, hKg, habsg⟩ :=
    exists_absolute_leftDerived_tensorModulePullback g Pg hg hgm
  obtain ⟨df, hdf⟩ := compatible_single_adjunction f Pf af Lf αf hLf habsf
  obtain ⟨dg, hdg⟩ := compatible_single_adjunction g Pg ag Lg αg hLg habsg
  let G := Pg.mapHomotopyCategory (.up ℤ) ⋙ Pf.mapHomotopyCategory (.up ℤ)
  let L := Lg ⋙ Lf
  let α : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight αg Lf ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Pg.mapHomotopyCategory (.up ℤ)) αf ≫
      (Functor.associator _ _ _).inv
  refine ⟨G, (ag.mapHomotopyCategory (.up ℤ)).comp
    (af.mapHomotopyCategory (.up ℤ)), L, dg.comp df, α, ?_, ?_⟩
  · intro K hK
    have := hKg K hK
    have hfiso : IsIso (αf.app ((Pg.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :=
      hKf ((Pg.mapHomologicalComplex (.up ℤ)).obj K)
        (tensorPullback_preserves_kFlat g Pg hg hgm K hK)
    have hi : IsIso
        (Lf.map (αg.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
          αf.app ((Pg.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := inferInstance
    simp only [α, G, L, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.id_comp, Category.comp_id]
    exact hi
  · intro K
    simp only [Adjunction.comp_unit_app, α, G, L, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp,
      Category.comp_id, Functor.comp_map, Functor.map_comp, Category.assoc]
    have hn := df.unit.naturality (αg.app K)
    dsimp at hn
    have hb := (moduleDirectImage g).rightDerivedFunctorUnit.naturality
      ((af.mapHomotopyCategory (.up ℤ)).unit.app
        ((Pg.mapHomotopyCategory (.up ℤ)).obj K))
    dsimp at hb
    rw [← (derivedModuleDirectImage g).map_comp_assoc, ← hn, Functor.map_comp]
    rw [Category.assoc, ← Functor.map_comp, hdf, Functor.map_comp]
    rw [← Category.assoc, hdg, Category.assoc]
    rw [← reassoc_of% hb]
    simp only [Functor.comp_obj]

end

end AlgebraicGeometry.RingedSpace
