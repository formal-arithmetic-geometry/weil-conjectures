/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.Paper.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Identity normalization for compactification refinement components

Source: blueprint main-20261015, det-sf-comp-coherence-cocycle, proof step 4;
Stacks Tag 0D6E (blueprint: lem-sf-compactification-refinement-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Scheme
set_option backward.isDefEq.respectTransparency false
universe v u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions C]

private theorem derivedId_fac (F : C ⥤ C) [F.Additive] (i : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso i ≪≫
        (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory i.hom (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let H := (HomotopyCategory.quotient C (.up ℤ)).obj K
  have hi := congrArg (fun e ↦ e.hom.app H) (Functor.mapDerivedCategoryIdIso_factorsh C)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hi
  have hf := NatTrans.congr_app
    (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac (𝟭 C)) H
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  simp only [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc]
  rw [show (Functor.rightDerivedFunctorNatIso i).hom =
    Functor.rightDerivedFunctorNatTrans i.hom from rfl]
  rw [Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app]
  simp only [Functor.whiskerRight_app, Category.assoc]
  rw [← Category.assoc ((𝟭 C).rightDerivedFunctorUnit.app _), hf]
  erw [Category.comp_id, Category.comp_id] at hi
  rw [hi]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl


private noncomputable def derivedId (F : C ⥤ C) [F.Additive] (i : F ≅ 𝟭 C) :
    F.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  Functor.rightDerivedFunctorNatIso i ≪≫
    (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso C

private lemma derivedId_fac' (F : C ⥤ C) [F.Additive] (i : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫ (derivedId F i).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory i.hom (.up ℤ)).app K) := by
  have h := derivedId_fac F i K
  rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

private lemma derivedId_inv_app (F : C ⥤ C) [F.Additive] (i : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    (derivedId F i).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app K) ≫
        F.rightDerivedFunctorUnit.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  apply (cancel_mono ((derivedId F i).hom.app _)).1
  rw [Iso.inv_hom_id_app, Category.assoc, derivedId_fac', ← Functor.map_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app, DerivedCategory.Qh.map_id]
  rfl


private lemma derived_left_unit (F : C ⥤ C) (G : C ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (i : F ≅ 𝟭 C) (e : F ⋙ G ≅ G)
    (he : Functor.whiskerRight i.inv G ≫ e.hom = 𝟙 G) :
    Functor.whiskerRight (derivedId F i).inv G.rightDerivedFunctor ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom = 𝟙 G.rightDerivedFunctor := by
  apply G.rightDerivedFunctor.rightDerived_ext G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let H := (HomotopyCategory.quotient C (.up ℤ)).obj K
  have hfac : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      ]
  have hfac2 := NatTrans.congr_app hfac H
  dsimp [Functor.rightDerivedFunctorCompUnit] at hfac2
  have hc := Functor.mapHomotopyCategoryCompIso_refl_hom_app (.up ℤ) F G H
  have hci : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app H =
      𝟙 _ := by
    apply (cancel_mono
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app H)).1
    rw [Iso.inv_hom_id_app, hc]
    erw [Category.id_comp]
    rfl
  rw [hci] at hfac2
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hfac2
  erw [Category.id_comp, Category.id_comp, Category.comp_id] at hfac2
  rw [Category.assoc] at hfac2
  have hnat := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app H)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hnat ⊢
  rw [derivedId_inv_app, Functor.map_comp]
  simp only [← Category.assoc]
  dsimp only [Functor.comp_map] at hnat
  erw [← hnat]
  rw [Category.assoc, Category.assoc]
  erw [hfac2]
  rw [← Category.assoc, ← Functor.map_comp]
  have hm : (G.mapHomotopyCategory (.up ℤ)).map
      ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app H) ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app H = 𝟙 _ := by
    change (NatTrans.mapHomotopyCategory (Functor.whiskerRight i.inv G) (.up ℤ)).app H ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app H = _
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, he]
    erw [NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    rfl
  rw [hm]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


namespace AlgebraicGeometry.ProEtale.CondensedRing
universe u
open scoped CategoryTheory.Obj
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private lemma refinementLowerStarId_eq (X : Scheme.{u}) :
    refinementLowerStarId Λ X = AlgebraicGeometry.ProEtale.CondensedRing.lowerStarId Λ X := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  exact (lowerStarId_hom_app_hom Λ X M).symm

private lemma derivedNatIso_comp {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasKInjectiveResolutions A]
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    (i : F ≅ G) (j : G ≅ H) :
    Functor.rightDerivedFunctorNatIso (i ≪≫ j) =
      Functor.rightDerivedFunctorNatIso i ≪≫ Functor.rightDerivedFunctorNatIso j := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]

omit [IsCommMonObj Λ] in
private lemma derivedNatIso_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    Functor.rightDerivedFunctorNatIso (eqToIso (congrArg (lowerStar Λ) h)) =
      eqToIso (congrArg (fun f ↦ (lowerStar Λ f).rightDerivedFunctor) h) := by
  subst g
  apply Iso.ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    eqToIso_refl]

private lemma refined_comp_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (lowerStar Λ g).rightDerivedFunctor.map ((refinementDerivedLowerStarId Λ X).inv.app M) ≫
      (refinementDerivedLowerStarComp Λ (𝟙 X) g).inv.app M ≫
      (eqToIso (congrArg (fun f ↦ (lowerStar Λ f).rightDerivedFunctor)
        (Category.id_comp g))).hom.app M = 𝟙 _ := by
  let := (upperStarLowerStarAdjunction Λ (𝟙 X)).preservesKInjectiveComplexes
  let e : lowerStar Λ (𝟙 X) ⋙ lowerStar Λ g ≅ lowerStar Λ g :=
    lowerStarComp Λ (𝟙 X) g ≪≫
      eqToIso (congrArg (lowerStar Λ) (Category.id_comp g))
  have he : Functor.whiskerRight (refinementLowerStarId Λ X).inv (lowerStar Λ g) ≫
      e.hom = 𝟙 _ := by
    rw [refinementLowerStarId_eq]
    change Functor.whiskerRight (lowerStarId Λ X).inv (lowerStar Λ g) ≫
      ((lowerStarComp Λ (𝟙 X) g).hom ≫
        (eqToIso (congrArg (lowerStar Λ) (Category.id_comp g))).hom) = 𝟙 _
    rw [lowerStarComp_id_left]
    simp only [lowerStarCongr, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
    rfl
  have hh := NatTrans.congr_app
    (derived_left_unit (lowerStar Λ (𝟙 X)) (lowerStar Λ g)
      (refinementLowerStarId Λ X) e he) M
  change (lowerStar Λ g).rightDerivedFunctor.map
      ((refinementDerivedLowerStarId Λ X).inv.app M) ≫
      (Functor.rightDerivedFunctorCompIso' (lowerStar Λ (𝟙 X)) (lowerStar Λ g) e).hom.app M =
      𝟙 _ at hh
  change (lowerStar Λ g).rightDerivedFunctor.map _ ≫
      ((Functor.rightDerivedFunctorCompIso (lowerStar Λ (𝟙 X)) (lowerStar Λ g)).inv ≫
        (Functor.rightDerivedFunctorNatIso
          (lowerStarComp Λ (𝟙 X) g ≪≫
            eqToIso (congrArg (lowerStar Λ) (Category.id_comp g)))).hom).app M = _ at hh
  rw [derivedNatIso_comp, derivedNatIso_eq (Λ := Λ) (Category.id_comp g)] at hh
  simpa only [refinementDerivedLowerStarComp, Iso.trans_inv, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_inv, Functor.rightDerivedFunctorNatIso,
    Iso.symm_hom, Category.assoc] using hh

/-- Identity normalization for the canonical compact-support refinement map of a dense
compactification in the geometric setting of Brown representability.

Source: blueprint main-20261015, det-sf-comp-coherence-cocycle, proof step 4;
det-sf-comp-coherence-refinement, proof steps 8--9; Stacks Tag 0D6E
(blueprint: lem-sf-compactification-refinement-identity).

Proof: the identity clause of localizingRefinement_coherence says that the open
refinement map followed by the derived identity identification is the identity. Cancel
that identification to express the refinement map as its inverse. Apply proper direct
image. The left unit law for the derived compositor follows by rightDerived_ext:
precomposing with its defining unit reduces the equation to lowerStarComp_id_left,
using naturality of the derived unit. Substitution gives the identity component. -/
theorem compactificationRefinementComponent_id
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification.DenseBoundaryCompactification f)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    compactificationRefinementComponent Λ (𝟙 c.obj) K = 𝟙 _ := by
  have h := (localizingRefinement_coherence Λ ℓ k p hp hpℓ hΛ f).2.2.1 c K
  have hh : localizingRefinementMap Λ (𝟙 c.obj) K =
      (refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).inv.app
        ((openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K) := by
    apply (cancel_mono ((refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).hom.app _)).1
    rw [h, Iso.inv_hom_id_app]
    rfl
  change (lowerStar Λ c.obj.obj.obj.g).rightDerivedFunctor.map
      (localizingRefinementMap Λ (𝟙 c.obj) K) ≫ _ = _
  rw [hh]
  exact refined_comp_unit Λ c.obj.obj.obj.g _

end AlgebraicGeometry.ProEtale.CondensedRing
