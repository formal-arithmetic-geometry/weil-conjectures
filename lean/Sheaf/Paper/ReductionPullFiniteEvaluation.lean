/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.CompletionMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Finite evaluation of the canonical strict tensor/pullback comparison

Source: Stacks Tags 03EL, 06YY, 099N(5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vModel vComplex vDerived
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.AdicSites

-- Keep tensor structures abstract while matching the derived comparison laws.
attribute [local irreducible] constantSheaf SheafOfModules.monoidalCategory
  HasDerivedCategory.standard

private theorem legacy_kflat {S : Site.{u}} {R : Sheaf S.topology CommRingCat.{u}}
    (P : CochainComplex (ConstantCompletion.Mod R) ℤ) (hP : P.IsKFlatTensor) :
    P.IsAcyclicTensorKFlat := hP

private theorem insertion_iso_properties {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {R B : Sheaf J CommRingCat.{u}} (c : R ≅ B) :
    (∀ M : ConstantCompletion.Mod R, IsIso (ConstantCompletion.insertion c.hom M)) ∧
      (∀ (M N : ConstantCompletion.Mod R) (h : M ⟶ N),
        (ConstantCompletion.underlying R).map h ≫ ConstantCompletion.insertion c.hom N =
          ConstantCompletion.insertion c.hom M ≫
            (ConstantCompletion.underlying B).map ((ConstantCompletion.change c.hom).map h)) := by
  obtain ⟨θ, _, hinv, hnat⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u, u, u, u} c
  have hi (M : ConstantCompletion.Mod R) : ConstantCompletion.insertion c.hom M =
      (ConstantCompletion.underlying B).map (θ M).inv := by
    apply (ConstantCompletion.insertion_existsUnique c.hom M).unique
    · exact (ConstantCompletion.insertion_existsUnique c.hom M).exists.choose_spec
    · intro U m
      exact hinv M U m
  constructor
  · intro M
    rw [hi]
    infer_instance
  · intro M N h
    rw [hi, hi]
    have hh : (ConstantCompletion.res c.inv).map h ≫ (θ N).inv =
        (θ M).inv ≫ (ConstantCompletion.change c.hom).map h := by
      apply (cancel_mono (θ N).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
      erw [hnat, Iso.inv_hom_id_assoc]
    exact congrArg (ConstantCompletion.underlying B).map hh

private theorem pullInsertion_properties {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    (∀ M : V.modules A, IsIso (ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra A) M)) ∧
    (∀ (M N : V.modules A) (h : M ⟶ N),
      f.inverse.map ((ConstantCompletion.underlying (V.ring A)).map h) ≫
        ConstantCompletion.pullInsertion f.algebra
          (ConstantCompletion.constantMap f.algebra A) N =
      ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A) M ≫
        (ConstantCompletion.underlying (U.ring A)).map ((f.modulePull A).map h)) := by
  have hc := insertion_iso_properties U.topology
    (f.algebra.constants.app (CommRingCat.of A))
  constructor
  · intro M
    have := hc.1 ((f.algebra.algebra (V.ring A)).modules.obj M)
    dsimp only [ConstantCompletion.pullInsertion, ConstantCompletion.constantMap]
    infer_instance
  · intro M N h
    have ha := (f.algebra.algebra (V.ring A)).moduleUnderlying.inv.naturality h
    dsimp only [Functor.comp_map] at ha
    have hb := hc.2 _ _ ((f.algebra.algebra (V.ring A)).modules.map h)
    dsimp only [ConstantCompletion.pullInsertion]
    erw [← Category.assoc, ha, Category.assoc, hb]
    rfl

private theorem finiteModuleUnit_underlying (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (M : S.modules A) :
    (ConstantCompletion.underlying (S.ring A)).map
        ((S.finiteModuleAdjunction A I n).unit.app M) =
      ConstantCompletion.insertion (ConstantCompletion.quotient S.topology A I n) M := by
  have h := (S.finiteModuleAdjunction_existsUnique A I n).exists.choose_spec M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

private theorem restricted_extension_hom_ext (S : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) (M : S.modules A)
    (N : S.modules (quotientRing A I n))
    {a b : (ConstantCompletion.res (ConstantCompletion.quotient S.topology A I n)).obj
        ((ConstantCompletion.change (ConstantCompletion.quotient S.topology A I n)).obj M) ⟶
      (ConstantCompletion.res (ConstantCompletion.quotient S.topology A I n)).obj N}
    (h : (S.finiteModuleAdjunction A I n).unit.app M ≫ a =
      (S.finiteModuleAdjunction A I n).unit.app M ≫ b) : a = b := by
  let φ := ConstantCompletion.quotient S.topology A I n
  let α := (sheafCompose S.topology (forget₂ CommRingCat RingCat)).map φ
  let : Presheaf.IsLocallySurjective S.topology α.hom :=
    Presheaf.isLocallySurjective_of_surjective S.topology α.hom (fun U ↦
      (ConstantCompletion.flat_and_quotients S.topology A I).2.2 n U.unop |>.1)
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective (α := α.hom)
    (M₁ := ((ConstantCompletion.change φ).obj M).val) (M₂ := N.val) N.isSheaf
  let a' : (ConstantCompletion.change φ).obj M ⟶ N := ⟨e.symm a.val⟩
  let b' : (ConstantCompletion.change φ).obj M ⟶ N := ⟨e.symm b.val⟩
  have ha : (ConstantCompletion.res φ).map a' = a := by
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply a.val
  have hb : (ConstantCompletion.res φ).map b' = b := by
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply b.val
  rw [← ha, ← hb]
  apply congrArg (ConstantCompletion.res φ).map
  apply ((S.finiteModuleAdjunction A I n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (S.finiteModuleAdjunction A I n).unit.app M ≫
    (ConstantCompletion.res φ).map a' =
      (S.finiteModuleAdjunction A I n).unit.app M ≫ (ConstantCompletion.res φ).map b'
  rw [ha, hb]
  exact h

private theorem moduleReductionPull_unit {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (M : V.modules A) (n : ℕ) :
    (U.finiteModuleAdjunction A I n).unit.app ((f.modulePull A).obj M) ≫
        ((f.moduleReductionPullIso A I).inv.app M).app (Opposite.op n) =
      (f.modulePull A).map ((V.finiteModuleAdjunction A I n).unit.app M) := by
  have hnorm := (f.moduleReductionPullIso_existsUnique A I).exists.choose_spec M n
  have hnat := (pullInsertion_properties f A).2 M _
    ((V.finiteModuleAdjunction A I n).unit.app M)
  rw [finiteModuleUnit_underlying] at hnat
  have h : (ConstantCompletion.underlying (U.ring A)).map
        ((f.modulePull A).map ((V.finiteModuleAdjunction A I n).unit.app M)) ≫
      (ConstantCompletion.underlying (U.ring A)).map
        (((f.moduleReductionPullIso A I).hom.app M).app (Opposite.op n)) =
      (ConstantCompletion.underlying (U.ring A)).map
        ((U.finiteModuleAdjunction A I n).unit.app ((f.modulePull A).obj M)) := by
    have := (pullInsertion_properties f A).1 M
    apply (cancel_epi (ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra A) M)).mp
    erw [← Category.assoc, ← hnat, Category.assoc, hnorm, finiteModuleUnit_underlying]
  have hmod := (ConstantCompletion.underlying (U.ring A)).map_injective
    ((CategoryTheory.Functor.map_comp _ _ _).trans h)
  apply (cancel_mono (((f.moduleReductionPullIso A I).app M).app (Opposite.op n)).hom).mp
  have hinv : ((f.moduleReductionPullIso A I).inv.app M).app (Opposite.op n) ≫
      ((f.moduleReductionPullIso A I).hom.app M).app (Opposite.op n) = 𝟙 _ :=
    congrArg (fun a ↦ a.app (Opposite.op n))
      (Iso.inv_hom_id_app (f.moduleReductionPullIso A I) M)
  erw [Category.assoc, hinv, Category.comp_id]
  exact hmod.symm

private theorem moduleReductionPull_finite {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : V.modules A) (n : ℕ) :
    ((f.moduleReductionPullIso A I).inv.app M).app (Opposite.op n) ≫
        (f.finiteModuleRestrictionPullIso A I n).hom.app
          ((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)).obj M) =
      (ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)).map
        ((ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n).hom.app M)
        := by
  apply restricted_extension_hom_ext U A I n ((f.modulePull A).obj M)
    ((f.modulePull (quotientRing A I n)).obj
      ((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)).obj M))
  rw [← Category.assoc, moduleReductionPull_unit]
  apply (ConstantCompletion.underlying (U.ring A)).map_injective
  have := (pullInsertion_properties f A).1 M
  apply (cancel_epi (ConstantCompletion.pullInsertion f.algebra
    (ConstantCompletion.constantMap f.algebra A) M)).mp
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  have hnat := (pullInsertion_properties f A).2 M _
    ((V.finiteModuleAdjunction A I n).unit.app M)
  rw [finiteModuleUnit_underlying] at hnat
  have hres := (f.finiteModuleRestrictionPullIso_existsUnique A I n).exists.choose_spec
    ((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)).obj M)
  erw [← Category.assoc, ← hnat, Category.assoc, hres, finiteModuleUnit_underlying]
  exact ((ConstantCompletion.ordinaryFinitePull_existsUnique f.algebra f.direct f.adjunction
    A I n).exists.choose_spec M).symm

private abbrev restrictionComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n)
      ).mapHomologicalComplex (.up ℤ) ⋙ (f.modulePull A).mapHomologicalComplex (.up ℤ) ≅
    (f.modulePull (quotientRing A I n)).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)
        ).mapHomologicalComplex (.up ℤ) :=
  ConstantCompletion.mapComplexSquare
    (ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n))
    (f.modulePull A) (f.modulePull (quotientRing A I n))
    (ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n))
    (f.finiteModuleRestrictionPullIso A I n)

private abbrev finiteComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (f.modulePull A).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n)
        ).mapHomologicalComplex (.up ℤ) ≅
    (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
      ).mapHomologicalComplex (.up ℤ) ⋙
      (f.modulePull (quotientRing A I n)).mapHomologicalComplex (.up ℤ) :=
  ConstantCompletion.mapComplexSquare (f.modulePull A)
    (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
    (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
    (f.modulePull (quotientRing A I n))
    (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n)

private theorem exact_square_factors
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app P) ≫
        G'.mapDerivedCategoryFactors.hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((ConstantCompletion.mapComplexSquare F G F' G' e).hom.app P) := by
  rw [ConstantCompletion.mapComplexSquare_hom]
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F G P
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors F' G' P
  have he := Functor.mapDerivedCategoryNatIso_fac e P
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hG, he, ← hF]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem flatOnSite_iff {S : Site.{u}} {R : Sheaf S.topology CommRingCat.{u}}
    (M : ConstantCompletion.Mod R) :
    M.IsFlat ↔ SheafOfModules.IsFlatOnSite (R := R) M := by
  let := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight M) ↔ _
  exact ⟨fun h ↦ ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso R M).symm h,
    fun h ↦ ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso R M) h⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pullback_kflat_bridge {V U : Site.{u}}
    {R : Sheaf V.topology CommRingCat.{u}}
    {S RI : Sheaf U.topology CommRingCat.{u}}
    (L : Sheaf V.topology (Type u) ⥤ Sheaf U.topology (Type u))
    (G : Sheaf U.topology (Type u) ⥤ Sheaf V.topology (Type u))
    (adj : L ⊣ G) [PreservesFiniteLimits L]
    (AI : SheafOfModules.AlgebraicInverseImage L R RI) (c : RI ⟶ S)
    (F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S)
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings c (AI.modules.obj M))
    (hmap : ∀ {M N} (a : M ⟶ N), F.map a = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c (AI.modules.obj M) (AI.modules.map a) ≫
        eqToHom (hobj N).symm) [F.Additive]
    (P : CochainComplex (ConstantCompletion.Mod R) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hflat : ∀ q : ℤ, (P.X q).IsFlat) :
    CochainComplex.IsAcyclicTensorKFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, (((F.mapHomologicalComplex (.up ℤ)).obj P).X q).IsFlat := by
  obtain ⟨hK, hterms⟩ := SheafOfModules.isKFlat_ringedToposPullback L G adj AI c
    F hobj hmap P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
    (fun q ↦ (flatOnSite_iff (P.X q)).mp (hflat q))
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hK,
    fun q ↦ (flatOnSite_iff _).mpr (hterms q)⟩

private theorem modulePull_kflat {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (P : CochainComplex (V.modules A) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hflat : ∀ q : ℤ, (P.X q).IsFlat) :
    CochainComplex.IsAcyclicTensorKFlat
      (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, ((((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P).X q).IsFlat := by
  exact pullback_kflat_bridge f.inverse f.direct f.adjunction
    (f.algebra.algebra (V.ring A)) (ConstantCompletion.constantMap f.algebra A)
    (f.modulePull A) (fun _ ↦ rfl)
    (fun _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    P hP hflat

private theorem exact_square_factors_cancel
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) :
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app P) ≫
      G'.mapDerivedCategoryFactors.hom.app
        ((F'.mapHomologicalComplex (.up ℤ)).obj P) =
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((ConstantCompletion.mapComplexSquare F G F' G' e).hom.app P) := by
  have h := exact_square_factors F G F' G' e P
  have hh := congrArg (fun a ↦ G.mapDerivedCategory.map
    (F.mapDerivedCategoryFactors.inv.app P) ≫ a) h
  simp only [← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  exact hh

private theorem restrictionPull_factors {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (P : CochainComplex (V.modules (quotientRing A I n)) ℤ) :
    (f.pull A).map
        ((ConstantCompletion.resFactors (ConstantCompletion.quotient V.topology A I n)
          ).hom.app P) ≫
      (f.finiteRestrictionPullIso A I n).hom.app
        ((ConstantCompletion.Q (V.ring (quotientRing A I n))).obj P) ≫
      (U.finiteRestriction A I n).map
        ((f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient U.topology A I n)).inv.app
        (((f.modulePull (quotientRing A I n)).mapHomologicalComplex (.up ℤ)).obj P) =
    (f.modulePull A).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring A)).map
        ((restrictionComplexIso f A I n).hom.app P) := by
  let φ := ConstantCompletion.quotient V.topology A I n
  let ψ := ConstantCompletion.quotient U.topology A I n
  let := HasDerivedCategory.standard (V.modules A)
  let := HasDerivedCategory.standard (U.modules A)
  let := HasDerivedCategory.standard (V.modules (quotientRing A I n))
  let := HasDerivedCategory.standard (U.modules (quotientRing A I n))
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  let := (siteRestrictScalars_exact ψ).1
  let := (siteRestrictScalars_exact ψ).2
  exact exact_square_factors_cancel (ConstantCompletion.res φ) (f.modulePull A)
    (f.modulePull (quotientRing A I n)) (ConstantCompletion.res ψ)
    (f.finiteModuleRestrictionPullIso A I n) P

private abbrev evaluationPullComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    (f.towerModulePull A).mapHomologicalComplex (.up ℤ) ⋙
      (U.evaluateModule A n).mapHomologicalComplex (.up ℤ) ≅
    (V.evaluateModule A n).mapHomologicalComplex (.up ℤ) ⋙
      (f.modulePull A).mapHomologicalComplex (.up ℤ) :=
  ConstantCompletion.mapComplexSquare (f.towerModulePull A) (U.evaluateModule A n)
    (V.evaluateModule A n) (f.modulePull A) (f.evaluateModulePullIso A n)

private theorem evaluatePull_factors {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) (P : CochainComplex (V.towers A) ℤ) :
    (f.evaluatePullIso A n).hom.app ((ConstantCompletion.TQ (V.ring A)).obj P) ≫
      (f.pull A).map ((V.evaluateModule A n).mapDerivedCategoryFactors.hom.app P) ≫
      (f.modulePull A).mapDerivedCategoryFactors.hom.app
        (((V.evaluateModule A n).mapHomologicalComplex (.up ℤ)).obj P) =
    (U.evaluate A n).map ((f.towerModulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (U.evaluateModule A n).mapDerivedCategoryFactors.hom.app
        (((f.towerModulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring A)).map
        ((evaluationPullComplexIso f A n).hom.app P) := by
  exact exact_square_factors (f.towerModulePull A) (U.evaluateModule A n)
    (V.evaluateModule A n) (f.modulePull A) (f.evaluateModulePullIso A n) P

private theorem postcompose_factors
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (L : C ⥤ D) (R : D ⥤ H) (G : C ⥤ E) (Q : E ⥤ H)
    (η : L ⋙ R ⟶ G ⋙ Q) {Z Z' : C} (v : Z ⟶ Z')
    {X Y : H} {W : E} {D₀ : D} (a : X ⟶ R.obj D₀)
    (b : D₀ ⟶ L.obj Z) (c : X ⟶ Y) (d : Y ⟶ Q.obj W)
    (w : W ⟶ G.obj Z)
    (h : a ≫ R.map b ≫ η.app Z = c ≫ d ≫ Q.map w) :
    a ≫ R.map (b ≫ L.map v) ≫ η.app Z' =
      c ≫ (d ≫ Q.map (w ≫ G.map v)) := by
  calc
    _ = (a ≫ R.map b ≫ η.app Z) ≫ Q.map (G.map v) := by
      simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
        congrArg (fun z ↦ a ≫ R.map b ≫ z) (η.naturality v)
    _ = (c ≫ d ≫ Q.map w) ≫ Q.map (G.map v) := by rw [h]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

private theorem naturality_paste_components
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y A B O : C} {M N : D} (r : X ⟶ Y)
    (x : X ⟶ A) (s : A ⟶ O) (u : Y ⟶ B) (v : B ⟶ O)
    (a : M ⟶ N) (ηX : M ⟶ Q.obj X) (ηY : N ⟶ Q.obj Y)
    (hn : a ≫ ηY = ηX ≫ Q.map r) (h : x ≫ s = r ≫ u ≫ v) :
    a ≫ (ηY ≫ Q.map u) ≫ Q.map v = (ηX ≫ Q.map x) ≫ Q.map s := by
  calc
    _ = (a ≫ ηY) ≫ Q.map (u ≫ v) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (ηX ≫ Q.map r) ≫ Q.map (u ≫ v) := by rw [hn]
    _ = ηX ≫ Q.map (r ≫ u ≫ v) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ηX ≫ Q.map (x ≫ s) := by rw [h]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

private theorem hom_comp_of_inv_comp {C : Type*} [Category C]
    {X Y Z : C} (e : X ≅ Y) {a : Y ⟶ Z} {b : X ⟶ Z}
    (h : e.inv ≫ b = a) : b = e.hom ≫ a := by
  rw [← h, Iso.hom_inv_id_assoc]

private theorem ordinary_reduction_cube {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (M : V.modules A) :
    (f.evaluateModulePullIso A n).hom.app
        ((ConstantCompletion.reductionTower V.topology A I false).obj M) ≫
      (f.modulePull A).map
        ((ConstantCompletion.quotientEvaluationIso V.topology A I n).hom.app M) ≫
      (f.finiteModuleRestrictionPullIso A I n).hom.app
        ((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)).obj M) =
    (U.evaluateModule A n).map ((f.moduleReductionPullIso A I).hom.app M) ≫
      (ConstantCompletion.quotientEvaluationIso U.topology A I n).hom.app
        ((f.modulePull A).obj M) ≫
      (ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)).map
        ((ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n
          ).hom.app M) := by
  have hh := hom_comp_of_inv_comp
    (((f.moduleReductionPullIso A I).app M).app (Opposite.op n))
    (moduleReductionPull_finite f A I M n)
  simp only [Morphism.evaluateModulePullIso, NatIso.ofComponents_hom_app,
    ConstantCompletion.quotientEvaluationIso, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  exact hh


private theorem mapComplexSquare_hom_f
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive D'] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (e : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) (q : ℤ) :
    ((ConstantCompletion.mapComplexSquare F G F' G' e).hom.app P).f q =
      e.hom.app (P.X q) := by
  rw [ConstantCompletion.mapComplexSquare_hom]
  rfl

private theorem complex_reduction_finite {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (V.modules A) ℤ) (n : ℕ) :
    (evaluationPullComplexIso f A n).hom.app
        (ConstantCompletion.reductionComplex V.topology A I false P) ≫
      ((f.modulePull A).mapHomologicalComplex (.up ℤ)).map
        ((ConstantCompletion.quotientEvaluationComplexIso V.topology A I n).hom.app P) ≫
      (restrictionComplexIso f A I n).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P) =
    ((U.evaluateModule A n).mapHomologicalComplex (.up ℤ)).map
        ((f.moduleReductionPullComplexIso A I).hom.app P) ≫
      (ConstantCompletion.quotientEvaluationComplexIso U.topology A I n).hom.app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)
        ).mapHomologicalComplex (.up ℤ)).map ((finiteComplexIso f A I n).hom.app P) := by
  have := ConstantCompletion.reductionTower_additive V.topology A I false
  have := ConstantCompletion.reductionTower_additive U.topology A I false
  dsimp only [evaluationPullComplexIso, restrictionComplexIso, finiteComplexIso,
    Morphism.moduleReductionPullComplexIso]
  apply HomologicalComplex.hom_ext
  intro q
  dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  simp only [ConstantCompletion.quotientEvaluationComplexIso_hom_f, mapComplexSquare_hom_f]
  dsimp only [ConstantCompletion.reductionComplex, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_X]
  simpa only [Functor.comp_obj, ConstantCompletion.quotientEvaluationIso,
    Iso.refl_hom, NatTrans.id_app]
    using ordinary_reduction_cube f A I n (P.X q)


private theorem map_two_eq_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z W T : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W} {d : W ⟶ T} {e : T ⟶ Z}
    (h : a ≫ b = c ≫ d ≫ e) :
    F.map a ≫ F.map b = F.map c ≫ F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem map_three_eq_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z W T U : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W}
    {d : X ⟶ T} {e : T ⟶ U} {g : U ⟶ W}
    (h : a ≫ b ≫ c = d ≫ e ≫ g) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map g := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem iso_naturality_cancel {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (a : X ⟶ Y) :
    e.hom.app X ≫ G.map a ≫ e.inv.app Y = F.map a := by
  rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem paste_finite
    {C : Type*} [Category C]
    {X Y Z W T U A₁ B₁ C₁ D₁ E₁ F₁ G₁ H₁ N₁ I₁ J₁ K₁ L₁ O : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W)
    (d : X ⟶ T) (e : T ⟶ U) (g : U ⟶ W)
    (k₁ : W ⟶ D₁) (k₂ : D₁ ⟶ E₁) (k₃ : E₁ ⟶ O)
    (l : Z ⟶ C₁) (c' : C₁ ⟶ D₁)
    (p₁ : Y ⟶ B₁) (p₂ : B₁ ⟶ F₁) (p₃ : F₁ ⟶ C₁)
    (a' : A₁ ⟶ B₁) (j₁ : X ⟶ A₁)
    (p₄ : F₁ ⟶ G₁) (q : G₁ ⟶ O)
    (j₂ : A₁ ⟶ H₁) (j₃ : H₁ ⟶ G₁)
    (g₁ : U ⟶ L₁) (g₂ : L₁ ⟶ J₁) (g₃ : J₁ ⟶ E₁)
    (e₁ : T ⟶ K₁) (e₂ : K₁ ⟶ L₁)
    (v₁ : K₁ ⟶ N₁) (v₂ : N₁ ⟶ I₁) (v₃ : I₁ ⟶ J₁)
    (r : H₁ ⟶ N₁) (v : I₁ ⟶ O)
    [Mono (k₁ ≫ k₂ ≫ k₃)]
    (h₁ : c ≫ k₁ = l ≫ c')
    (h₂ : b ≫ l = p₁ ≫ p₂ ≫ p₃)
    (h₃ : a ≫ p₁ = j₁ ≫ a')
    (h₄ : p₃ ≫ c' ≫ k₂ ≫ k₃ = p₄ ≫ q)
    (h₅ : a' ≫ p₂ ≫ p₄ = j₂ ≫ j₃)
    (h₆ : g ≫ k₁ ≫ k₂ = g₁ ≫ g₂ ≫ g₃)
    (h₇ : e ≫ g₁ = e₁ ≫ e₂)
    (h₈ : e₂ ≫ g₂ = v₁ ≫ v₂ ≫ v₃)
    (h₉ : v₃ ≫ g₃ ≫ k₃ = v)
    (h₁₀ : d ≫ e₁ ≫ v₁ = j₁ ≫ j₂ ≫ r)
    (h₁₁ : r ≫ v₂ ≫ v = j₃ ≫ q) : a ≫ b ≫ c = d ≫ e ≫ g := by
  apply (cancel_mono (k₁ ≫ k₂ ≫ k₃)).mp
  simp only [Category.assoc]
  calc
    a ≫ b ≫ c ≫ k₁ ≫ k₂ ≫ k₃ = j₁ ≫ j₂ ≫ j₃ ≫ q := by
      rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]
    _ = j₁ ≫ j₂ ≫ r ≫ v₂ ≫ v := by rw [← h₁₁]
    _ = d ≫ e ≫ g ≫ k₁ ≫ k₂ ≫ k₃ := by
      symm
      rw [reassoc_of% h₆, reassoc_of% h₇, reassoc_of% h₈, h₉,
        reassoc_of% h₁₀]

private theorem NatTrans.app_eq_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α β : F ⟶ G) {X Y : C} (e : X ≅ Y)
    (h : α.app X = β.app X) : α.app Y = β.app Y := by
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, h]

private theorem iso_inv_comp_of_comp_eq {C : Type*} [Category C]
    {X Y Z : C} (e : X ≅ Y) {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : a = e.hom ≫ b) : e.inv ≫ a = b := by
  rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

-- Only the component equations at the chosen representative enter the pasting argument.
private theorem finite_model_abstract
    {C D B E V W C' D' B' E' V' W' : Type vModel}
    [Category.{vComplex} C] [Category.{vComplex} D] [Category.{vComplex} B] [Category.{vComplex}
      E] [Category.{vComplex} V] [Category.{vComplex} W]
    [Category.{vDerived} C'] [Category.{vDerived} D'] [Category.{vDerived} B']
      [Category.{vDerived} E'] [Category.{vDerived} V'] [Category.{vDerived} W']
    (F : C ⥤ D)
    (T : V ⥤ W)
    (ev : V ⥤ C)
    (eu : W ⥤ D)
    (rv : C ⥤ V)
    (ru : D ⥤ W)
    (xv : C ⥤ B)
    (xu : D ⥤ E)
    (sv : B ⥤ C)
    (su : E ⥤ D)
    (G : B ⥤ E)
    (DF : C' ⥤ D')
    (DT : V' ⥤ W')
    (EV : V' ⥤ C')
    (EU : W' ⥤ D')
    (SV : B' ⥤ C')
    (SU : E' ⥤ D')
    (DG : B' ⥤ E')
    (RV : C' ⥤ V')
    (RU : D' ⥤ W')
    (XV : C' ⥤ B')
    (XU : D' ⥤ E')
    (QC : C ⥤ C')
    (QD : D ⥤ D')
    (QB : B ⥤ B')
    (QE : E ⥤ E')
    (QV : V ⥤ V')
    (QW : W ⥤ W')
    (P : C)
    (fF : QC ⋙ DF ≅ F ⋙ QD)
    (fT : QV ⋙ DT ≅ T ⋙ QW)
    (fEV : QV ⋙ EV ≅ ev ⋙ QC)
    (fEU : QW ⋙ EU ≅ eu ⋙ QD)
    (fSV : sv ⋙ QC ≅ QB ⋙ SV)
    (fSU : su ⋙ QD ≅ QE ⋙ SU)
    (fG : QB ⋙ DG ≅ G ⋙ QE)
    (cRV : QC ⋙ RV ⟶ rv ⋙ QV)
    (cRU : QD ⋙ RU ⟶ ru ⋙ QW)
    (cXV : QC ⋙ XV ⟶ xv ⋙ QB)
    (cXU : QD ⋙ XU ⟶ xu ⋙ QE)
    (evalSquare : T ⋙ eu ≅ ev ⋙ F)
    (finiteEvalV : rv ⋙ ev ≅ xv ⋙ sv)
    (restrictSquare : sv ⋙ F ≅ G ⋙ su)
    (reductionSquare : rv ⋙ T ≅ F ⋙ ru)
    (finiteEvalU : ru ⋙ eu ≅ xu ⋙ su)
    (finiteSquare : F ⋙ xu ≅ xv ⋙ G)
    (evalIso : DT ⋙ EU ≅ EV ⋙ DF)
    (finiteEvalIsoV : RV ⋙ EV ≅ XV ⋙ SV)
    (restrictionIso : SV ⋙ DF ≅ DG ⋙ SU)
    (reductionIso : RV ⋙ DT ≅ DF ⋙ RU)
    (finiteEvalIsoU : RU ⋙ EU ≅ XU ⋙ SU)
    (finiteIso : DF ⋙ XU ≅ XV ⋙ DG)
    (isoC : IsIso (cXV.app P))
    (hRestrict : DF.map (fSV.hom.app (xv.obj P)) ≫ restrictionIso.hom.app (QB.obj (xv.obj P)) ≫
      SU.map (fG.hom.app (xv.obj P)) ≫ fSU.inv.app (G.obj (xv.obj P)) =
    fF.hom.app (sv.obj (xv.obj P)) ≫ QD.map (restrictSquare.hom.app (xv.obj P)))
    (hEval : evalIso.hom.app (QV.obj (rv.obj P)) ≫ DF.map (fEV.hom.app (rv.obj P)) ≫
      fF.hom.app (ev.obj (rv.obj P)) =
    EU.map (fT.hom.app (rv.obj P)) ≫ fEU.hom.app (T.obj (rv.obj P)) ≫
      QD.map (evalSquare.hom.app (rv.obj P)))
    (hFinite : XU.map (fF.hom.app P) ≫ cXU.app (F.obj P) ≫
      QE.map (finiteSquare.hom.app P) =
    finiteIso.hom.app (QC.obj P) ≫ DG.map (cXV.app P) ≫
      fG.hom.app (xv.obj P))
    (hBV : finiteEvalIsoV.hom.app (QC.obj P) ≫ SV.map (cXV.app P) =
    EV.map (cRV.app P) ≫
      (fEV.hom.app (rv.obj P) ≫ QC.map (finiteEvalV.hom.app P)) ≫
      fSV.hom.app (xv.obj P))
    (hBU : finiteEvalIsoU.hom.app (QD.obj (F.obj P)) ≫
        SU.map (cXU.app (F.obj P)) =
    EU.map (cRU.app (F.obj P)) ≫
      (fEU.hom.app (ru.obj (F.obj P)) ≫
        QD.map (finiteEvalU.hom.app (F.obj P))) ≫
      fSU.hom.app (xu.obj (F.obj P)))
    (hReduction : reductionIso.hom.app (QC.obj P) ≫ RU.map (fF.hom.app P) ≫
      cRU.app (F.obj P) =
    DT.map (cRV.app P) ≫ fT.hom.app (rv.obj P) ≫
      QW.map (reductionSquare.hom.app P))
    (hCube : evalSquare.hom.app (rv.obj P) ≫ F.map (finiteEvalV.hom.app P) ≫
      restrictSquare.hom.app (xv.obj P) =
    eu.map (reductionSquare.hom.app P) ≫
      finiteEvalU.hom.app (F.obj P) ≫ su.map (finiteSquare.hom.app P)) :
    evalIso.hom.app (RV.obj (QC.obj P)) ≫
        DF.map (finiteEvalIsoV.hom.app (QC.obj P)) ≫
        restrictionIso.hom.app (XV.obj (QC.obj P)) =
      EU.map (reductionIso.hom.app (QC.obj P)) ≫
        finiteEvalIsoU.hom.app (DF.obj (QC.obj P)) ≫
        SU.map (finiteIso.hom.app (QC.obj P)) := by
  let : IsIso (cXV.app P) := isoC
  let XP := rv.obj P
  let YP := xv.obj P
  let fP := F.obj P
  let ZP := G.obj YP
  let cV := cRV.app P
  let c := cXV.app P
  let r := reductionSquare.hom.app P
  let t := finiteSquare.hom.app P
  let vV := finiteEvalV.hom.app P
  let vU := finiteEvalU.hom.app fP
  let x := evalSquare.hom.app XP ≫ F.map vV
  let k₁ := SU.map (DG.map c)
  let k₂ := SU.map (fG.hom.app YP)
  let k₃ := fSU.inv.app ZP
  have : IsIso (k₁ ≫ k₂ ≫ k₃) := by dsimp only [k₁, k₂, k₃]; infer_instance
  refine paste_finite
    (evalIso.hom.app (RV.obj (QC.obj P)))
    (DF.map (finiteEvalIsoV.hom.app (QC.obj P)))
    (restrictionIso.hom.app (XV.obj (QC.obj P)))
    (EU.map (reductionIso.hom.app (QC.obj P)))
    (finiteEvalIsoU.hom.app (DF.obj (QC.obj P)))
    (SU.map (finiteIso.hom.app (QC.obj P)))
    k₁ k₂ k₃
    (DF.map (SV.map c)) (restrictionIso.hom.app
      (QB.obj YP))
    (DF.map (EV.map cV))
    (DF.map (fEV.hom.app XP ≫ QC.map vV))
    (DF.map (fSV.hom.app YP))
    (evalIso.hom.app (QV.obj XP))
    (EU.map (DT.map cV))
    (fF.hom.app (sv.obj YP))
    (QD.map (restrictSquare.hom.app YP))
    (EU.map (fT.hom.app XP))
    (fEU.hom.app (T.obj XP) ≫ QD.map x)
    (SU.map (XU.map (fF.hom.app P)))
    (SU.map (cXU.app fP))
    (SU.map (QE.map t))
    (EU.map (RU.map (fF.hom.app P)))
    (finiteEvalIsoU.hom.app (QD.obj fP))
    (EU.map (cRU.app fP))
    (fEU.hom.app (ru.obj fP) ≫ QD.map vU)
    (fSU.hom.app (xu.obj fP))
    (EU.map (QW.map r))
    (QD.map (su.map t))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (restrictionIso.hom.naturality c).symm
  · exact map_two_eq_three DF hBV
  · exact (evalIso.hom.naturality cV).symm
  · exact hRestrict
  · exact postcompose_factors QC DF F QD
      fF.hom
      (Z := ev.obj XP) (Z' := sv.obj YP) vV
      (evalIso.hom.app (QV.obj XP)) (fEV.hom.app XP)
      (EU.map (fT.hom.app XP)) (fEU.hom.app
        (T.obj XP))
      (evalSquare.hom.app XP) hEval
  · exact map_three_eq_three SU hFinite.symm
  · exact (finiteEvalIsoU.hom.naturality (fF.hom.app P)).symm
  · exact hBU
  · exact iso_naturality_cancel fSU t
  · exact map_three_eq_three EU hReduction
  · exact naturality_paste_components QD (eu.map r)
      x (restrictSquare.hom.app YP) vU (su.map t) _ _ _
      (by simpa only [XP, fP, Functor.comp_obj, Functor.comp_map] using
        fEU.hom.naturality r)
      (by simpa only [x, XP, YP, r, t, vU, vV, fP, Category.assoc] using hCube)



private theorem finite_model_transport
    {C' D' B' E' V' W' : Type vModel}
    [Category.{vDerived} C'] [Category.{vDerived} D'] [Category.{vDerived} B']
    [Category.{vDerived} E'] [Category.{vDerived} V'] [Category.{vDerived} W']
    (DF : C' ⥤ D')
    (DT : V' ⥤ W')
    (EV : V' ⥤ C')
    (EU : W' ⥤ D')
    (SV : B' ⥤ C')
    (SU : E' ⥤ D')
    (DG : B' ⥤ E')
    (RV : C' ⥤ V')
    (RU : D' ⥤ W')
    (XV : C' ⥤ B')
    (XU : D' ⥤ E')
    (evalIso : DT ⋙ EU ≅ EV ⋙ DF)
    (finiteEvalIsoV : RV ⋙ EV ≅ XV ⋙ SV)
    (restrictionIso : SV ⋙ DF ≅ DG ⋙ SU)
    (reductionIso : RV ⋙ DT ≅ DF ⋙ RU)
    (finiteEvalIsoU : RU ⋙ EU ≅ XU ⋙ SU)
    (finiteIso : DF ⋙ XU ≅ XV ⋙ DG)
    {X Y : C'} (e : X ≅ Y)
    (h : evalIso.hom.app (RV.obj X) ≫
        DF.map (finiteEvalIsoV.hom.app X) ≫
        restrictionIso.hom.app (XV.obj X) =
      EU.map (reductionIso.hom.app X) ≫
        finiteEvalIsoU.hom.app (DF.obj X) ≫ SU.map
          (finiteIso.hom.app X)) :
    evalIso.hom.app (RV.obj Y) ≫
        DF.map (finiteEvalIsoV.hom.app Y) ≫
        restrictionIso.hom.app (XV.obj Y) =
      EU.map (reductionIso.hom.app Y) ≫
        finiteEvalIsoU.hom.app (DF.obj Y) ≫ SU.map
          (finiteIso.hom.app Y) := by
  let α : RV ⋙ DT ⋙ EU ⟶ XV ⋙ DG ⋙
    SU :=
    Functor.whiskerLeft RV evalIso.hom ≫
      Functor.whiskerRight finiteEvalIsoV.hom DF ≫
      Functor.whiskerLeft XV restrictionIso.hom
  let β : RV ⋙ DT ⋙ EU ⟶ XV ⋙ DG ⋙
    SU :=
    Functor.whiskerRight reductionIso.hom EU ≫
      Functor.whiskerLeft DF finiteEvalIsoU.hom ≫
      Functor.whiskerRight finiteIso.hom SU
  have hx : α.app X = β.app X := by
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    exact h
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using NatTrans.app_eq_of_iso α β e hx


private theorem finite_model_on_resolution {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (V.modules A) ℤ) (hP : P.IsAcyclicTensorKFlat)
    (hflat : ∀ q : ℤ, (P.X q).IsFlat) (n : ℕ) :
    let K₀ := (ConstantCompletion.Q (V.ring A)).obj P
    (f.evaluatePullIso A n).hom.app ((V.reduction A I).obj K₀) ≫
        (f.pull A).map ((V.finiteEvaluationIso A I n).hom.app K₀) ≫
        (f.finiteRestrictionPullIso A I n).hom.app ((V.finiteReduction A I n).obj K₀) =
      (U.evaluate A n).map ((f.reductionPullIso A I).hom.app K₀) ≫
        (U.finiteEvaluationIso A I n).hom.app ((f.pull A).obj K₀) ≫
        (U.finiteRestriction A I n).map ((f.finitePullIso A I n).hom.app K₀) := by
  let := ConstantCompletion.reductionTower_additive V.topology A I false
  let := ConstantCompletion.reductionTower_additive U.topology A I false
  have hpull := modulePull_kflat f A P hP hflat
  exact finite_model_abstract
    ((f.modulePull A).mapHomologicalComplex (.up ℤ))
    ((f.towerModulePull A).mapHomologicalComplex (.up ℤ))
    ((V.evaluateModule A n).mapHomologicalComplex (.up ℤ))
    ((U.evaluateModule A n).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.reductionTower V.topology A I false
      ).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.reductionTower U.topology A I false
      ).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
      ).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n)
      ).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n)
      ).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)
      ).mapHomologicalComplex (.up ℤ))
    ((f.modulePull (quotientRing A I n)).mapHomologicalComplex (.up ℤ))
    (f.pull A)
    (f.towerPull A)
    (V.evaluate A n)
    (U.evaluate A n)
    (V.finiteRestriction A I n)
    (U.finiteRestriction A I n)
    (f.pull (quotientRing A I n))
    (V.reduction A I)
    (U.reduction A I)
    (V.finiteReduction A I n)
    (U.finiteReduction A I n)
    (ConstantCompletion.Q (V.ring A))
    (ConstantCompletion.Q (U.ring A))
    (ConstantCompletion.Q (V.ring (quotientRing A I n)))
    (ConstantCompletion.Q (U.ring (quotientRing A I n)))
    (ConstantCompletion.TQ (V.ring A))
    (ConstantCompletion.TQ (U.ring A))
    P
    ((f.modulePull A).mapDerivedCategoryFactors)
    ((f.towerModulePull A).mapDerivedCategoryFactors)
    ((V.evaluateModule A n).mapDerivedCategoryFactors)
    ((U.evaluateModule A n).mapDerivedCategoryFactors)
    (ConstantCompletion.resFactors (ConstantCompletion.quotient V.topology A I n))
    (ConstantCompletion.resFactors (ConstantCompletion.quotient U.topology A I n))
    ((f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors)
    ((ConstantCompletion.quotientPresentation V.topology A I false).comparison)
    ((ConstantCompletion.quotientPresentation U.topology A I false).comparison)
    (ConstantCompletion.extendComparison (ConstantCompletion.quotient V.topology A I n))
    (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n))
    (evaluationPullComplexIso f A n)
    (ConstantCompletion.quotientEvaluationComplexIso V.topology A I n)
    (restrictionComplexIso f A I n)
    (f.moduleReductionPullComplexIso A I)
    (ConstantCompletion.quotientEvaluationComplexIso U.topology A I n)
    (finiteComplexIso f A I n)
    (f.evaluatePullIso A n)
    (V.finiteEvaluationIso A I n)
    (f.finiteRestrictionPullIso A I n)
    (f.reductionPullIso A I)
    (U.finiteEvaluationIso A I n)
    (f.finitePullIso A I n)
    (((ConstantCompletion.derivedExtension
      (ConstantCompletion.quotient V.topology A I n)).computation) P hP)
    (restrictionPull_factors f A I n
      (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
        ).mapHomologicalComplex (.up ℤ)).obj P))
    ((evaluatePull_factors f A n) (((ConstantCompletion.reductionTower V.topology A I false
      ).mapHomologicalComplex (.up ℤ)).obj P))
    (((f.finitePullIso_existsUnique A I n).exists.choose_spec) P hP hflat)
    (((V.finiteEvaluationIso_existsUnique A I n).exists.choose_spec) P hP hflat)
    ((U.finiteEvaluationIso_existsUnique A I n).exists.choose_spec
      (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) hpull.1 hpull.2)
    (((f.reductionPullIso_existsUnique A I).exists.choose_spec) P hP hflat)
    (complex_reduction_finite f A I P n)

/-- Evaluation of the strict tensor comparison retains its finite quotient action.

Source: Stacks Tags 03EL, 06YY, 099N(5)
(blueprint: lem-sf-reduction-pull-finite-evaluation).

Proof: take one flat-term K-flat representative P. Use the defining normalization of
reductionPullIso, and evaluate its ordinary strict tensor comparison at n. The defining
normalizations of finiteEvaluationIso and finitePullIso identify the two reduction
counits with this same finite quotient tensor calculation. At the module level both
maps send the inverse image of a pure tensor to the same pure tensor. The normalization
of finiteModuleRestrictionPullIso identifies the two restricted actions. Thus the
square commutes on P, including all scalar restrictions. Pullback preserves the
resolving class and its quasi-isomorphisms. Descend the equality through the K-flat
localization; every derived object has such a representative. No completeness
assumption is needed. Noetherianness is used only for the sectionwise quotient API. -/
theorem reductionPullFiniteEvaluation {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.evaluate A n).map ((f.reductionPullIso A I).inv.app K) ≫
        (f.evaluatePullIso A n).hom.app ((V.reduction A I).obj K) ≫
        (f.pull A).map ((V.finiteEvaluationIso A I n).hom.app K) ≫
        (f.finiteRestrictionPullIso A I n).hom.app ((V.finiteReduction A I n).obj K) =
      (U.finiteEvaluationIso A I n).hom.app ((f.pull A).obj K) ≫
        (U.finiteRestriction A I n).map ((f.finitePullIso A I n).hom.app K) := by
  obtain ⟨P, q, hP, hflat, hq, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := V.ring A) ((ConstantCompletion.Q (V.ring A)).objPreimage K)
  let : QuasiIso q := hq
  have : IsIso ((ConstantCompletion.Q (V.ring A)).map q) := inferInstance
  obtain ⟨e⟩ : Nonempty ((ConstantCompletion.Q (V.ring A)).obj P ≅ K) :=
    ⟨asIso ((ConstantCompletion.Q (V.ring A)).map q) ≪≫
      (ConstantCompletion.Q (V.ring A)).objObjPreimageIso K⟩
  have hp := finite_model_on_resolution f A I P (legacy_kflat P hP) hflat n
  have hk := finite_model_transport
    (f.pull A)
    (f.towerPull A)
    (V.evaluate A n)
    (U.evaluate A n)
    (V.finiteRestriction A I n)
    (U.finiteRestriction A I n)
    (f.pull (quotientRing A I n))
    (V.reduction A I)
    (U.reduction A I)
    (V.finiteReduction A I n)
    (U.finiteReduction A I n)
    (f.evaluatePullIso A n)
    (V.finiteEvaluationIso A I n)
    (f.finiteRestrictionPullIso A I n)
    (f.reductionPullIso A I)
    (U.finiteEvaluationIso A I n)
    (f.finitePullIso A I n)
    e hp
  exact iso_inv_comp_of_comp_eq
    ((U.evaluate A n).mapIso ((f.reductionPullIso A I).app K)) hk

end CategoryTheory.AdicSites
