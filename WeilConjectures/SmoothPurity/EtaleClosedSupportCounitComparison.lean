/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import all WeilConjectures.AlgebraicGeometry.EtaleInjectiveSupportSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.CategoryTheory.UnboundedSectionsLocalization.UnboundedSectionsLocalization

/-! # The ordinary closed-support counit comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]

omit [Abelian.HasKInjectiveResolutions D] in
private theorem exactObjQ (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorObjQIso I).hom =
      F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj I) ≫
        F.mapDerivedCategoryFactors.hom.app I := by
  have h := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  have hf := F.mapDerivedCategoryFactorsh_hom_app I
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, asIso_inv]
  have qh : (DerivedCategory.quotientCompQhIso C).inv.app I = 𝟙 _ := rfl
  have qd : (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I) = 𝟙 _ := rfl
  erw [qh, qd, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hi : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I = 𝟙 _ := rfl
  rw [hi] at hf
  have qh' : (DerivedCategory.quotientCompQhIso C).hom.app I = 𝟙 _ := rfl
  have qd' : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I) = 𝟙 _ := rfl
  rw [qh', qd'] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hf
  apply (cancel_epi (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj I))).mp
  rw [IsIso.hom_inv_id, ← Category.assoc]
  erw [h]
  rw [← hf, Iso.inv_hom_id_app]

private theorem compObjQ (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (I : CochainComplex C ℤ) [I.IsKInjective] :
    (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Q.obj I) ≫
        (H.rightDerivedFunctorObjQIso I).hom =
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.rightDerivedFunctorNatIso]
  rw [Category.assoc, Functor.rightDerivedFunctorNatTrans_app_Q_obj]
  rw [← Category.assoc,
    ← CategoryTheory.UnboundedSectionsLocalization.compIso_objQ F G I]
  simp only [Iso.inv_hom_id_app_assoc, Category.assoc]

private theorem counitObjQ (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesKInjectiveComplexes] (a : L ⊣ R)
    (I : CochainComplex D ℤ) [I.IsKInjective] :
    (L.rightDerivedFunctorObjQIso
        ((R.mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
      L.rightDerivedFunctor.map (R.rightDerivedFunctorObjQIso I).inv ≫
      (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
        L.rightDerivedFunctorIsoMapDerivedCategory.symm).counit.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  let ad := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    L.rightDerivedFunctorIsoMapDerivedCategory.symm
  have h := derivedCounit_Q_normalized a ad I
  have he : (L.rightDerivedFunctorObjQIso
      ((R.mapHomologicalComplex (.up ℤ)).obj I)).inv =
    L.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.rightDerivedFunctorIsoMapDerivedCategory.inv.app
        (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj I)) := by
    have hx : L.rightDerivedFunctorObjQIso
        ((R.mapHomologicalComplex (.up ℤ)).obj I) =
      L.rightDerivedFunctorIsoMapDerivedCategory.app
        (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj I)) ≪≫
      L.mapDerivedCategoryFactors.app ((R.mapHomologicalComplex (.up ℤ)).obj I) :=
      Iso.ext (exactObjQ L _)
    rw [hx]
    rfl
  rw [he]
  simpa only [ad, Adjunction.rightAdjointUniq_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Functor.map_comp, Category.assoc] using h

/-- Derivation preserves a kernel-inclusion formula for a closed adjunction.
Source: the injective-kernel construction in `lem-pur-supported-hom.proof.md`
(blueprint: lem-pur-etale-closed-support-counit-comparison).
Proof: use a K-injective representative I. The derived compositors become their
canonical computing isomorphisms on I, RI and LRI. The ordinary inclusion equation
holds degree by degree. The exact left functor and the derived adjunction normalize
the counit to the same complex map. Cancel the computing isomorphisms, then use
naturality along an isomorphism to a K-injective representative for any input. -/
theorem derivedKernelCounit (L : C ⥤ D) (R : D ⥤ C)
    (GX : D ⥤ E) (GZ : C ⥤ E) (S : D ⥤ E)
    [L.Additive] [R.Additive] [GX.Additive] [GZ.Additive] [S.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesKInjectiveComplexes] [R.PreservesKInjectiveComplexes]
    (a : L ⊣ R) (e : L ⋙ GX ≅ GZ) (r : R ⋙ GZ ≅ S) (b : S ⟶ GX)
    (hb : ∀ M, e.hom.app (R.obj M) ≫ r.hom.app M ≫ b.app M =
      GX.map (a.counit.app M)) :
    Functor.whiskerLeft R.rightDerivedFunctor
        (Functor.rightDerivedFunctorCompIso' L GX e).hom ≫
      (Functor.rightDerivedFunctorCompIso' R GZ r).hom ≫
      Functor.rightDerivedFunctorNatTrans b =
    Functor.whiskerRight
      (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
        L.rightDerivedFunctorIsoMapDerivedCategory.symm).counit GX.rightDerivedFunctor := by
  let ad := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    L.rightDerivedFunctorIsoMapDerivedCategory.symm
  apply NatTrans.ext
  funext M
  obtain ⟨I, hI, ⟨z⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hI
  let A := Functor.whiskerLeft R.rightDerivedFunctor
      (Functor.rightDerivedFunctorCompIso' L GX e).hom ≫
    (Functor.rightDerivedFunctorCompIso' R GZ r).hom ≫
    Functor.rightDerivedFunctorNatTrans b
  let B := Functor.whiskerRight ad.counit GX.rightDerivedFunctor
  have hQ : A.app (DerivedCategory.Q.obj I) = B.app (DerivedCategory.Q.obj I) := by
    let J := (R.mapHomologicalComplex (.up ℤ)).obj I
    let K := (L.mapHomologicalComplex (.up ℤ)).obj J
    have : CochainComplex.IsKInjective
        ((R.mapHomologicalComplex (.up ℤ) ⋙ L.mapHomologicalComplex (.up ℤ)).obj I) := by
      change CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj I))
      infer_instance
    apply (cancel_mono (GX.rightDerivedFunctorObjQIso I).hom).mp
    apply (cancel_epi (GX.rightDerivedFunctor.map
      (L.rightDerivedFunctor.map (R.rightDerivedFunctorObjQIso I).inv))).mp
    apply (cancel_epi (GX.rightDerivedFunctor.map (L.rightDerivedFunctorObjQIso J).inv)).mp
    apply (cancel_epi (GX.rightDerivedFunctorObjQIso K).inv).mp
    dsimp only [A, B, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    rw [Functor.rightDerivedFunctorNatTrans_app_Q_obj]
    erw [(Functor.rightDerivedFunctorCompIso' L GX e).hom.naturality_assoc]
    rw [reassoc_of% compObjQ R GZ S r I]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [reassoc_of% compObjQ L GX GZ e J]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← DerivedCategory.Q.map_comp]
    dsimp only [K]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
    have hc : (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J ≫
        (NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex b (.up ℤ)).app I =
      (GX.mapHomologicalComplex (.up ℤ)).map
        ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
      ext n
      exact hb (I.X n)
    rw [hc]
    erw [counitObjQ L R a I,
      Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom]
    change _ = (GX.rightDerivedFunctorObjQIso K).inv ≫
      (GX.rightDerivedFunctorObjQIso K).hom ≫ _
    simp only [Iso.inv_hom_id_assoc]
  have hnA := A.naturality z.hom
  have hnB := B.naturality z.hom
  apply (cancel_mono (GX.rightDerivedFunctor.map z.hom)).mp
  exact hnA.symm.trans ((congrArg (fun t ↦
    (R.rightDerivedFunctor ⋙ L.rightDerivedFunctor ⋙ GX.rightDerivedFunctor).map z.hom ≫ t)
      hQ).trans hnB)

end
