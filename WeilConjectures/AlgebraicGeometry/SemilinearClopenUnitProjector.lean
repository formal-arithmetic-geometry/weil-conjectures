/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRingProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.VaryingRingModulePiComplementZero
import all WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The specified clopen unit on semilinear systems

Source: Stacks Project, sites-modules.tex, Tag 03DI (lemma-extension-by-zero),
and derived.tex, Tag 015F (lemma-right-derived-exact-functor), specialized to a
clopen decomposition on the ringed sequence site
(blueprint: lem-sf-semilinear-clopen-unit-projector).

All maps below act on the whole ordinary unbounded derived category of strict
semilinear systems. The projector is localized from the existing ordinary map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.VaryingRing

attribute [local irreducible] exactAdj Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Functor.rightDerivedFunctor

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The derived open unit is invertible, including for the empty clopen.
Source: Stacks 03DI; proof steps 1--5
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: restriction of ordinary extension is the identity, with precisely the ordinary
open unit. Localize the exact adjunction and its invertible unit; the normalized
right-derived/exact comparison identifies this with the specified jAdj unit. -/
theorem semilinearClopen_openUnit_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (jAdj R φ s).unit := by
  have := moduleJAdj_unit_isIso R φ s
  let e : J R φ s ⋙ G R φ s ≅ 𝟭 (Derived R φ U) :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (moduleJAdj R φ s).unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso _
  exact (jAdj R φ s).isIso_unit_of_iso e

/-- The specified transpose of the inverse open unit, with no choice of isomorphism.
Source: Stacks 03DI; proof step 5
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenToDirect {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : J R φ s ⟶ P R φ s :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (J R φ s) (adj R φ s).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (jAdj R φ s).unit (semilinearClopen_openUnit_isIso R φ s))
      (P R φ s) ≫ (Functor.leftUnitor _).hom

/-- The actual termwise localization of the ordinary identity/zero projector.
Source: Stacks 03DI; proof steps 3 and 5
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenPi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Derived R φ X) ⟶ G R φ s ⋙ J R φ s :=
  (Functor.mapDerivedCategoryIdIso _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R φ X) (.up ℤ)) _ _
      (𝟭 (Modules R φ X)).mapDerivedCategory
      (pull R φ s ⋙ extension R φ s).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (modulePi R φ s) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

private theorem clopenToDirect_app {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : Derived R φ U) :
    (clopenToDirect R φ s).app N = (adj R φ s).unit.app ((J R φ s).obj N) ≫
      (P R φ s).map ((@inv _ _ _ _ (jAdj R φ s).unit
        (semilinearClopen_openUnit_isIso R φ s)).app N) := by
  dsimp only [clopenToDirect, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

attribute [local irreducible] clopenToDirect

/-- Clopen direct image is exact on actual ordinary systems.
Source: Stacks 03DI, 03DJ; proof steps 1--4
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: sheaf gluing on the two disjoint clopen pieces gives the product of section
modules, including zero sections on the empty object. Direct image is the first
factor with zero second factor, hence canonically isomorphic to exact extension by
zero via moduleOpenToP. Transfer finite-colimit preservation across this isomorphism. -/
theorem semilinearClopen_push_colimits {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : PreservesFiniteColimits (push R φ s) := by
  have := moduleOpenToP_isIso R φ s
  exact preservesFiniteColimits_of_natIso (asIso (moduleOpenToP R φ s))

/-- The exactness witness used by the canonical exact/right-derived comparison.
Source: Stacks 015F (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
instance semilinearClopen_pushColimits {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : PreservesFiniteColimits (push R φ s) :=
  semilinearClopen_push_colimits R φ s

private theorem mate_isIso_of_rightAdjoints
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {P Q : B ⥤ A} {L' : C ⥤ D} {P' Q' : D ⥤ C}
    (a : L ⊣ P) (qa : L ⊣ Q) (b : L' ⊣ P') (qb : L' ⊣ Q')
    {E : A ⥤ C} {E' : B ⥤ D} (d : E ⋙ L' ⟶ L ⋙ E')
    [IsIso (mateEquiv qa qb d).natTrans] :
    IsIso (mateEquiv a b d).natTrans := by
  have h (M : B) : (mateEquiv a b d).app M ≫
      (b.rightAdjointUniq qb).hom.app (E'.obj M) =
    E.map ((a.rightAdjointUniq qa).hom.app M) ≫ (mateEquiv qa qb d).app M := by
    apply (qb.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [b.rightAdjointUniq_hom_app_counit qb, mateEquiv_counit,
      mateEquiv_counit]
    rw [← Category.assoc, ← Functor.comp_map E L', d.naturality]
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← E'.map_comp, a.rightAdjointUniq_hom_app_counit qa]
  have hi (M : B) : IsIso ((mateEquiv a b d).app M) := by
    have : IsIso ((mateEquiv a b d).app M ≫
        (b.rightAdjointUniq qb).hom.app (E'.obj M)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((b.rightAdjointUniq qb).hom.app (E'.obj M))
  exact NatIso.isIso_of_isIso_app _

private theorem exactAdj_eq_rightDerived
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : L ⊣ P) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      P.rightDerivedFunctorIsoMapDerivedCategory = exactAdj a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
    P.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K))).mp
  have hη := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom P.rightDerivedFunctorUnit K
  have hn := P.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hr := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  change (a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    P.rightDerivedFunctorIsoMapDerivedCategory.hom.app _) ≫ _ = _
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at hη
  rw [Category.assoc, ← reassoc_of% hn, ← Category.assoc, hη,
    Category.assoc, ← Category.assoc (P.rightDerivedFunctorUnit.app _) _ _, hr,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact (exactAdj_unit a K).symm

private theorem exactAdj_isoUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : L ⊣ P)
    [IsIso a.unit] :
    (exactAdj a).unit = (Functor.mapDerivedCategoryIdIso A).inv ≫
      (Functor.mapDerivedCategoryNatIso (asIso a.unit)).hom ≫
      (Functor.mapDerivedCategoryCompIso L P).hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
    P.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [NatTrans.comp_app, Category.assoc]
  rw [exactAdj_unit, Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

private theorem derivedCompId_fach
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ 𝟭 A) (K : HomotopyCategory A (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
        (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryNatIso_fach,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factorsh F G K]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem localizedTranspose
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {L : A ⥤ B} {P J₀ : B ⥤ A} [L.Additive] [P.Additive] [J₀.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
    (a : L ⊣ P) (κ : J₀ ≅ P) (β : J₀ ⋙ L ≅ 𝟭 B)
    (hκ : ∀ M, a.unit.app (J₀.obj M) ≫ P.map (β.hom.app M) = κ.hom.app M) :
    ∀ M : DerivedCategory B,
      (exactAdj a).unit.app (J₀.mapDerivedCategory.obj M) ≫
        P.mapDerivedCategory.map
          (((Functor.mapDerivedCategoryCompIso J₀ L).symm ≪≫
            Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryIdIso B).hom.app M) =
        (Functor.mapDerivedCategoryNatIso κ).hom.app M := by
  suffices h : Functor.whiskerLeft J₀.mapDerivedCategory (exactAdj a).unit ≫
      Functor.whiskerRight
        (((Functor.mapDerivedCategoryCompIso J₀ L).symm ≪≫
          Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryIdIso B).hom)
        P.mapDerivedCategory = (Functor.mapDerivedCategoryNatIso κ).hom by
    intro M
    exact congr_app h M
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_epi (J₀.mapDerivedCategoryFactorsh.inv.app K)).mp
  apply (cancel_mono (P.mapDerivedCategoryFactorsh.hom.app K)).mp
  have hn := (exactAdj a).unit.naturality (J₀.mapDerivedCategoryFactorsh.inv.app K)
  change _ ≫ (exactAdj a).unit.app _ =
    (exactAdj a).unit.app _ ≫ P.mapDerivedCategory.map
      (L.mapDerivedCategory.map (J₀.mapDerivedCategoryFactorsh.inv.app K)) at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn, derivedCompId_fach]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [P.mapDerivedCategoryFactorsh.hom.naturality]
  erw [reassoc_of% (exactAdj_unit a ((J₀.mapHomotopyCategory (.up ℤ)).obj K))]
  dsimp only [Functor.comp_map]
  rw [← DerivedCategory.Qh.map_comp, Functor.mapDerivedCategoryNatIso_fach]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (a.mapHomotopyCategory (.up ℤ)).unit.app
    ((HomotopyCategory.quotient A (.up ℤ)).obj
      ((J₀.mapHomologicalComplex (.up ℤ)).obj K)) ≫ _ = _
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient _ _).map _ ≫
      (HomotopyCategory.quotient _ _).map _ = (HomotopyCategory.quotient _ _).map _
  rw [← Functor.map_comp]
  congr 1
  ext n : 1
  exact hκ _

section LocalizedMaps
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {F H : A ⥤ B} [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private def derivedMap (t : F ⟶ H) : F.mapDerivedCategory ⟶ H.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    _ _ _ _ (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q)

private theorem derivedMap_fac (t : F ⟶ H) (K : CochainComplex A ℤ) :
    (derivedMap t).app (DerivedCategory.Q.obj K) ≫ H.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  dsimp only [derivedMap]
  rw [Localization.liftNatTrans_app]
  change (_ ≫ _ ≫ H.mapDerivedCategoryFactors.inv.app K) ≫
    H.mapDerivedCategoryFactors.hom.app K = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem derivedMap_fach (t : F ⟶ H) (K : HomotopyCategory A (.up ℤ)) :
    (derivedMap t).app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory t (.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hnt : (NatTrans.mapHomotopyCategory t (.up ℤ)).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      (HomotopyCategory.quotient B (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := rfl
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app, hnt,
    ← NatTrans.naturality_assoc, reassoc_of% (derivedMap_fac t K),
    reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K))]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.id_comp]
end LocalizedMaps

private theorem clopenPi_fach {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (K : HomotopyCategory (Modules R φ X) (.up ℤ)) :
    (clopenPi R φ s).app (DerivedCategory.Qh.obj K) ≫
        (J R φ s).map ((pull R φ s).mapDerivedCategoryFactorsh.hom.app K) ≫
        (extension R φ s).mapDerivedCategoryFactorsh.hom.app
          (((pull R φ s).mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (modulePi R φ s) (.up ℤ)).app K) := by
  change ((Functor.mapDerivedCategoryIdIso _).inv ≫ derivedMap (modulePi R φ s) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom).app _ ≫ _ = _
  simp only [NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh, derivedMap_fach,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem clopenToDirect_localized {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenToDirect R φ s ≫ (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom =
      (Functor.mapDerivedCategoryNatIso
        (@asIso _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s))).hom := by
  have := moduleJAdj_unit_isIso R φ s
  have := semilinearClopen_openUnit_isIso R φ s
  have hj : jAdj R φ s = exactAdj (moduleJAdj R φ s) :=
    exactAdj_eq_rightDerived (moduleJAdj R φ s)
  have hu := exactAdj_isoUnit (moduleJAdj R φ s)
  rw [← hj] at hu
  have hi : inv (jAdj R φ s).unit =
      ((Functor.mapDerivedCategoryCompIso (extension R φ s) (pull R φ s)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (asIso (moduleJAdj R φ s).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso (Modules R φ U)).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hu]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact (Functor.mapDerivedCategoryIdIso _).inv_hom_id
  ext M
  have ht := localizedTranspose (moduleAdj R φ s)
    (@asIso _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s))
    (asIso (moduleJAdj R φ s).unit).symm
    (fun N ↦ by
      dsimp only [moduleOpenToP, NatTrans.comp_app, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Iso.symm_hom]
      rfl) M
  rw [← hi] at ht
  have he := congr_app (congrArg Adjunction.unit
    (exactAdj_eq_rightDerived (moduleAdj R φ s))) ((J R φ s).obj M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at he
  have hn := (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((inv (jAdj R φ s).unit).app M)
  simp only [NatTrans.comp_app, clopenToDirect_app]
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [Category.assoc, hn, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ (push R φ s).mapDerivedCategory.map
    ((inv (jAdj R φ s).unit).app M)) he).trans ht

private theorem clopenToDirect_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (clopenToDirect R φ s) := by
  have hi : IsIso (clopenToDirect R φ s ≫
      (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom) := by
    rw [clopenToDirect_localized]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom

private theorem clopenPi_toDirect {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenPi R φ s ≫ Functor.whiskerLeft (G R φ s) (clopenToDirect R φ s) =
      (adj R φ s).unit := by
  have := moduleOpenToP_isIso R φ s
  let κ := @asIso _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s)
  let e := (push R φ s).rightDerivedFunctorIsoMapDerivedCategory
  apply (cancel_mono (Functor.whiskerLeft (G R φ s) e.hom)).mp
  have he := congrArg Adjunction.unit (exactAdj_eq_rightDerived (moduleAdj R φ s))
  change (adj R φ s).unit ≫ Functor.whiskerLeft (G R φ s) e.hom =
    (exactAdj (moduleAdj R φ s)).unit at he
  rw [Category.assoc, ← Functor.whiskerLeft_comp, clopenToDirect_localized, he]
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules R φ X) (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono ((push R φ s).mapDerivedCategory.map
      ((pull R φ s).mapDerivedCategoryFactorsh.hom.app K) ≫
    (push R φ s).mapDerivedCategoryFactorsh.hom.app
      (((pull R φ s).mapHomotopyCategory (.up ℤ)).obj K))).mp
  have hn := (Functor.mapDerivedCategoryNatIso κ).hom.naturality
    ((pull R φ s).mapDerivedCategoryFactorsh.hom.app K)
  rw [Category.assoc, ← reassoc_of% hn, Functor.mapDerivedCategoryNatIso_fach]
  rw [reassoc_of% (clopenPi_fach R φ s K),
    exactAdj_unit, ← DerivedCategory.Qh.map_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient _ _).map _ ≫
      (HomotopyCategory.quotient _ _).map _ = (HomotopyCategory.quotient _ _).map _
  rw [← Functor.map_comp]
  congr 1
  ext n : 1
  change (moduleAdj R φ s).unit.app _ ≫ (inv (moduleOpenToP R φ s)).app _ ≫
    (moduleOpenToP R φ s).app _ = _
  simp
  rfl

/-- The component projector is precisely the specified direct-image unit.
Source: Stacks 03DI and 015F; proof steps 1--5
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: on a test object H, split H into its pullbacks to U and C. The disjoint sheaf
cover gives M(H) = M(H_U) × M(H_C), with M(empty) = 0. All restrictions, scalars and
semilinear transitions preserve the factors. Direct image is the first factor.
The left-adjoint uniqueness comparison from extension by zero has transpose the
inverse open unit, so is exactly moduleOpenToP. Its inverse after the right unit is
modulePi, identity on U and zero on C. Thus its composite with moduleOpenToP is the
right unit, restriction to U is the open unit, and restriction to C is zero.
Exactness identifies total right-derived direct image with termwise direct image
(lem-weil-pbc-exact-functor-derived-functor). Localize the ordinary isomorphism
(lem-sfb-exact-derived-natural-iso) and both normalized adjunctions
(def-weil-exact-derived-adjunction). The transpose remains the inverse open unit,
identifying the localized map with clopenToDirect. Localizing the three ordinary
identities proves the displayed whole-system identities and the representative
normalization. No equality of derived morphisms is inferred from evaluation. -/
theorem semilinearClopen_unit_projector {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) :
    IsIso (clopenToDirect R φ s) ∧
    clopenPi R φ s ≫ Functor.whiskerLeft (G R φ s) (clopenToDirect R φ s) =
      (adj R φ s).unit ∧
    (∀ M : Derived R φ X,
      (G R φ s).map ((clopenPi R φ s).app M) =
        (jAdj R φ s).unit.app ((G R φ s).obj M)) ∧
    (∀ M : Derived R φ X, (G R φ c).map ((clopenPi R φ s).app M) = 0) ∧
    (∀ K : CochainComplex (Modules R φ U) ℤ,
      (clopenToDirect R φ s).app (DerivedCategory.Q.obj K) ≫
          (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom.app
            (DerivedCategory.Q.obj K) ≫
          (push R φ s).mapDerivedCategoryFactors.hom.app K =
        (extension R φ s).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (moduleOpenToP R φ s) (.up ℤ)).app K)) := by
  have ht := clopenToDirect_isIso R φ s
  have hu := semilinearClopen_openUnit_isIso R φ s
  have hp := clopenPi_toDirect R φ s
  refine ⟨ht, hp, ?_, ?_, ?_⟩
  · intro M
    let t : Adjunction.Triple (J R φ s) (G R φ s) (P R φ s) :=
      ⟨jAdj R φ s, adj R φ s⟩
    let ff := (jAdj R φ s).fullyFaithfulLOfIsIsoUnit
    have := ff.full
    have := ff.faithful
    have he : clopenToDirect R φ s = t.leftToRight := by
      ext N
      simp [clopenToDirect, t, Adjunction.Triple.leftToRight]
    apply (cancel_mono ((G R φ s).map
      ((clopenToDirect R φ s).app ((G R φ s).obj M)))).mp
    rw [← Functor.map_comp]
    have hp' := congr_app hp M
    change (clopenPi R φ s).app M ≫
      (clopenToDirect R φ s).app ((G R φ s).obj M) = (adj R φ s).unit.app M at hp'
    rw [hp', he, t.leftToRight_app_obj, Functor.map_comp]
    change _ = (jAdj R φ s).unit.app _ ≫
      (G R φ s).map ((jAdj R φ s).counit.app M) ≫ _
    rw [← Category.assoc, (jAdj R φ s).right_triangle_components]
    exact (Category.id_comp _).symm
  · intro M
    have hd : Disjoint (Set.range s) (Set.range c) := by
      rw [hc]
      exact disjoint_compl_right
    let F := extension R φ s ⋙ pull R φ c
    have hz (N : Modules R φ U) : IsZero (F.obj N) :=
      disjoint_extension R φ s c hd N
    have hzD := F.isZero_mapDerivedCategory_obj ((G R φ s).obj M) (fun _ ↦ hz _)
    have hzT := hzD.of_iso
      ((Functor.mapDerivedCategoryCompIso (extension R φ s) (pull R φ c)).app
        ((G R φ s).obj M)).symm
    exact hzT.eq_of_tgt _ _
  · intro K
    rw [← Category.assoc, ← NatTrans.comp_app, clopenToDirect_localized]
    exact Functor.mapDerivedCategoryNatIso_fac _ K


section Coefficients

variable (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
  (α : ∀ n : ℕ, R n ⟶ D n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ ψ n = φ n ≫ α n)

/-- The actual map of constant coefficient sheaves.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientMap (X : Scheme.{u}) (n : ℕ) :
    coefficients R X n ⟶ coefficients D X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (α n)

include hα in
/-- Compatibility of the actual coefficient sheaf maps.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: apply the constant-sheaf functor to hα and its functorial composition equation. -/
theorem clopenCoefficientMap_commute (X : Scheme.{u}) (n : ℕ) :
    clopenCoefficientMap R D α X (n + 1) ≫ coefficientTransition D ψ X n =
      coefficientTransition R φ X n ≫ clopenCoefficientMap R D α X n := by
  change (constantSheaf (Scheme.ProEt.topology X) CommRingCat).map (α (n + 1)) ≫
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat).map (ψ n) =
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat).map (φ n) ≫
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat).map (α n)
  rw [← Functor.map_comp, ← Functor.map_comp, hα n]

/-- Restriction along the actual map of ringed sequence sites.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
abbrev clopenCoefficientRestriction (X : Scheme.{u}) : Modules D ψ X ⥤ Modules R φ X :=
  SemilinearSections.res
    (SemilinearSections.systemMap (Scheme.ProEt.topology X)
      (coefficients R X) (coefficientTransition R φ X)
      (coefficients D X) (coefficientTransition D ψ X) (clopenCoefficientMap R D α X)
      (clopenCoefficientMap_commute R φ D ψ α hα X))

/-- Exact derived restriction on whole systems.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
abbrev clopenCoefficientRes (X : Scheme.{u}) : Derived D ψ X ⥤ Derived R φ X :=
  (clopenCoefficientRestriction R φ D ψ α hα X).mapDerivedCategory

/-- The dependency's K-flat scalar-extension model for the actual coefficient map.
Source: proof step 6; lem-coef-semilinear-derived-sections
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientScalar (X : Scheme.{u}) :=
  (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)).some.coefficientExtension
      (coefficients D X) (coefficientTransition D ψ X)
      (clopenCoefficientMap R D α X) (clopenCoefficientMap_commute R φ D ψ α hα X)

attribute [local irreducible] clopenCoefficientScalar

private def coefficientRing (Y : Scheme.{u}) : seqRing R φ Y ⟶ seqRing D ψ Y := (sheafCompose
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (SemilinearSections.systemMap (Scheme.ProEt.topology Y)
        (coefficients R Y) (coefficientTransition R φ Y)
        (coefficients D Y) (coefficientTransition D ψ Y) (clopenCoefficientMap R D α Y)
        (clopenCoefficientMap_commute R φ D ψ α hα Y))

private theorem coefficientRing_app (Y : Scheme.{u}) (V : (ℕ × Y.ProEt)ᵒᵖ) :
      (coefficientRing R φ D ψ α hα Y).hom.app V = (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((clopenCoefficientMap R D α Y V.unop.1).hom.app (op V.unop.2)) := by
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map f)
      ((SemilinearSections.systemMap_existsUnique (Scheme.ProEt.topology Y)
        (coefficients R Y) (coefficientTransition R φ Y)
        (coefficients D Y) (coefficientTransition D ψ Y) (clopenCoefficientMap R D α Y)
        (clopenCoefficientMap_commute R φ D ψ α hα Y)).exists.choose_spec
        V.unop.1 (op V.unop.2))

private theorem coefficientRing_naturality {U X : Scheme.{u}} (s : U ⟶ X) :
    coefficientRing R φ D ψ α hα X ≫ ringMap D ψ s = ringMap R φ s ≫
      ((baseChange s).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceTopology (Scheme.ProEt.topology U))).map
          (coefficientRing R φ D ψ α hα U) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (coefficientRing R φ D ψ α hα X).hom.app V ≫ ringMapApp D s V =
      ringMapApp R s V ≫ (coefficientRing R φ D ψ α hα U).hom.app ((baseChange s).op.obj V)
    rw [coefficientRing_app, coefficientRing_app]
    exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map
      (congrArg (fun f ↦ f.hom.app (op V.unop.2))
        (constantMap_naturality s (α V.unop.1)))

/-- The ordinary direct-image comparison is uniquely the identity on sections.
Source: Stacks 03DI, proof steps 1 and 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: both sides at (n,H) are the sections of M_n on H times_X U with the same
R_n action via α_n. Identity maps are linear and commute with restrictions and
semilinear transitions. Sectionwise extensionality proves uniqueness. -/
theorem clopenCoefficientPush_existsUnique {U X : Scheme.{u}} (s : U ⟶ X) :
    ∃! d : clopenCoefficientRestriction R φ D ψ α hα U ⋙ push R φ s ≅
        push D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα X,
      ∀ (M : Modules D ψ U) (n : ℕ) (H : X.ProEt)
        (x : (((clopenCoefficientRestriction R φ D ψ α hα U ⋙ push R φ s).obj M).val.obj
          (op (n, H)))),
        HEq ((d.hom.app M).val.app (op (n, H)) x) x := by
  let a := coefficientRing R φ D ψ α hα
  have he := coefficientRing_naturality R φ D ψ α hα s
  let d : clopenCoefficientRestriction R φ D ψ α hα U ⋙ push R φ s ≅
      push D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα X :=
    SheafOfModules.pushforwardComp (F := baseChange s) (G := 𝟭 _)
      (K' := coefficientSequenceTopology (Scheme.ProEt.topology U))
      (R' := seqRing D ψ U) (ringMap R φ s) (a U) ≪≫
      SheafOfModules.pushforwardCongr he.symm ≪≫
      (SheafOfModules.pushforwardComp (F := 𝟭 _) (G := baseChange s)
        (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
        (K' := coefficientSequenceTopology (Scheme.ProEt.topology U))
        (R := seqRing D ψ X) (R' := seqRing D ψ U) (a X) (ringMap D ψ s)).symm
  refine ⟨d, fun _ _ _ _ ↦ HEq.rfl, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext V x
  exact eq_of_heq (hd' M V.unop.1 V.unop.2 x)

/-- The identity-on-sections ordinary pushforward comparison.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientPush {U X : Scheme.{u}} (s : U ⟶ X) :=
  (clopenCoefficientPush_existsUnique R φ D ψ α hα s).choose

private theorem coefficientPush_inv_sections {U X : Scheme.{u}} (s : U ⟶ X)
    (M : Modules D ψ U) (V : (ℕ × X.ProEt)ᵒᵖ)
    (x : (((push D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα X).obj M).val.obj V)) :
    ((clopenCoefficientPush R φ D ψ α hα s).inv.app M).val.app V x = x := by
  have hh : ((clopenCoefficientPush R φ D ψ α hα s).hom.app M).val.app V x = x :=
    eq_of_heq ((clopenCoefficientPush_existsUnique R φ D ψ α hα s).choose_spec.1
      M V.unop.1 V.unop.2 x)
  have h := congrArg (fun f ↦ f.val.app V x)
    ((clopenCoefficientPush R φ D ψ α hα s).hom_inv_id_app M)
  change ((clopenCoefficientPush R φ D ψ α hα s).inv.app M).val.app V
    (((clopenCoefficientPush R φ D ψ α hα s).hom.app M).val.app V x) = x at h
  rw [hh] at h
  exact h

/-- The ordinary inverse-image comparison is the mate of sectionwise restriction.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientPullInv {U X : Scheme.{u}} (s : U ⟶ X) :
    clopenCoefficientRestriction R φ D ψ α hα X ⋙ pull R φ s ⟶
      pull D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα U :=
  (mateEquiv (moduleAdj D ψ s) (moduleAdj R φ s)).symm
    (clopenCoefficientPush R φ D ψ α hα s).inv

attribute [local instance] prodOpenContinuous baseChange_continuous

private theorem coefficientOpenRing_naturality {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] :
    (((𝟭 ℕ).prod (openMap s)).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology U))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).map
        (coefficientRing R φ D ψ α hα X) ≫ openRingTranspose D ψ s =
      openRingTranspose R φ s ≫ coefficientRing R φ D ψ α hα U := by
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange s)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceTopology (Scheme.ProEt.topology U)) := baseChange_continuous s
  exact ((prodAdj (openAdj s)).sheafPushforwardContinuous
    (E := RingCat.{u + 1})
    (coefficientSequenceTopology (Scheme.ProEt.topology U))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))).homEquiv_naturality_right_square
      _ _ _ _ (coefficientRing_naturality R φ D ψ α hα s)

attribute [local instance] openRingTranspose_isIso

private def coefficientOpenRestrictionIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] :
    SheafOfModules.pushforward (inv (openRingTranspose D ψ s)) ⋙
        clopenCoefficientRestriction R φ D ψ α hα U ≅
      clopenCoefficientRestriction R φ D ψ α hα X ⋙
        SheafOfModules.pushforward (inv (openRingTranspose R φ s)) := by
  let a := coefficientRing R φ D ψ α hα
  let F := (𝟭 ℕ).prod (openMap s)
  have := prodOpenContinuous s
  have := openRingTranspose_isIso R φ s
  have := openRingTranspose_isIso D ψ s
  have he : a U ≫ inv (openRingTranspose D ψ s) =
      inv (openRingTranspose R φ s) ≫
        (F.sheafPushforwardContinuous RingCat.{u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology U))
          (coefficientSequenceTopology (Scheme.ProEt.topology X))).map (a X) := by
    apply (cancel_epi (openRingTranspose R φ s)).mp
    apply (cancel_mono (openRingTranspose D ψ s)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
    exact (coefficientOpenRing_naturality R φ D ψ α hα s).symm
  exact (SheafOfModules.pushforwardComp (F := F) (G := 𝟭 _)
      (K' := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R' := seqRing D ψ X) (inv (openRingTranspose R φ s)) (a X) ≪≫
    SheafOfModules.pushforwardCongr he.symm ≪≫
    (SheafOfModules.pushforwardComp (F := 𝟭 _) (G := F)
      (K := coefficientSequenceTopology (Scheme.ProEt.topology U))
      (K' := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R := seqRing D ψ U) (R' := seqRing D ψ X)
      (a U) (inv (openRingTranspose D ψ s))).symm).symm

private theorem coefficientOpenRestrictionIso_unit {U X : Scheme.{u}} (s : U ⟶ X)
  [IsOpenImmersion s] (M : Modules D ψ X) :
    (clopenCoefficientRestriction R φ D ψ α hα X).map
        ((openPullAdj D ψ s).unit.app M) ≫
      (clopenCoefficientPush R φ D ψ α hα s).inv.app
        ((SheafOfModules.pushforward (inv (openRingTranspose D ψ s))).obj M) ≫
      (push R φ s).map ((coefficientOpenRestrictionIso R φ D ψ α hα s).hom.app M) =
    (openPullAdj R φ s).unit.app
      ((clopenCoefficientRestriction R φ D ψ α hα X).obj M) := by
  ext V x
  change _ = M.val.map ((prodAdj (openAdj s)).counit.app V.unop).op x
  change ((clopenCoefficientPush R φ D ψ α hα s).inv.app
    ((SheafOfModules.pushforward (inv (openRingTranspose D ψ s))).obj M)).val.app V
      (M.val.map ((prodAdj (openAdj s)).counit.app V.unop).op x) = _
  exact coefficientPush_inv_sections R φ D ψ α hα s _ _ _

/-- Coefficient restriction commutes with clopen restriction.
Source: Stacks 03DI; proof steps 1 and 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: on the two-factor section decomposition pullback selects the first factor;
restriction of scalars leaves both factors unchanged. The identity comparison has
exactly the ordinary mate normalization, so the displayed mate is invertible. -/
theorem clopenCoefficientPullInv_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientPullInv R φ D ψ α hα s) := by
  let q := coefficientOpenRestrictionIso R φ D ψ α hα s
  unfold clopenCoefficientPullInv
  exact inverseMateIsoOfUnit (moduleAdj D ψ s) (moduleAdj R φ s)
    (clopenCoefficientRestriction R φ D ψ α hα X)
    (clopenCoefficientRestriction R φ D ψ α hα U)
    (clopenCoefficientPush R φ D ψ α hα s).inv
    (Functor.isoWhiskerRight ((moduleAdj D ψ s).leftAdjointUniq (openPullAdj D ψ s)) _ ≪≫
      q ≪≫ Functor.isoWhiskerLeft _
        ((moduleAdj R φ s).leftAdjointUniq (openPullAdj R φ s)).symm)
    (transportedUnit (moduleAdj D ψ s) (openPullAdj D ψ s)
      (moduleAdj R φ s) (openPullAdj R φ s)
      (clopenCoefficientRestriction R φ D ψ α hα X)
      (clopenCoefficientRestriction R φ D ψ α hα U)
      (clopenCoefficientPush R φ D ψ α hα s).symm q
      (coefficientOpenRestrictionIso_unit R φ D ψ α hα s))


/-- Localize the actual ordinary coefficient/restriction comparison.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientG {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenCoefficientRes R φ D ψ α hα X ⋙ G R φ s ≅
      G D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα U :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (clopenCoefficientPullInv R φ D ψ α hα s)
        (clopenCoefficientPullInv_isIso R φ D ψ α hα s)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The open-extension coefficient comparison is fixed by the open adjunction mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientJInv {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenCoefficientRes R φ D ψ α hα U ⋙ J R φ s ⟶
      J D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα X :=
  (mateEquiv (jAdj D ψ s) (jAdj R φ s)).symm
    (clopenCoefficientG R φ D ψ α hα s).inv

/-- The direct-image coefficient comparison is fixed by the right adjunction mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientP {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    P D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα X ⟶
      clopenCoefficientRes R φ D ψ α hα U ⋙ P R φ s :=
  mateEquiv (adj D ψ s) (adj R φ s) (clopenCoefficientG R φ D ψ α hα s).hom

/-- The coefficient/direct-image mate is invertible for clopen direct image.
Source: Stacks 03DI and 015F; proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: localize the inverse of clopenCoefficientPush. Clopen direct image is exact,
so its canonical exact/right-derived comparison identifies the localization with
the displayed derived mate, with the same units and counits. -/
theorem clopenCoefficientP_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientP R φ D ψ α hα s) := by
  have := clopenCoefficientPullInv_isIso R φ D ψ α hα s
  let d := (clopenCoefficientPush R φ D ψ α hα s).symm
  let β := asIso (clopenCoefficientPullInv R φ D ψ α hα s)
  let a := exactAdj (moduleAdj D ψ s)
  let b := exactAdj (moduleAdj R φ s)
  have hβ (M : Modules D ψ X) :
      (moduleAdj R φ s).unit.app
          ((clopenCoefficientRestriction R φ D ψ α hα X).obj M) ≫
        (push R φ s).map (β.hom.app M) =
      (clopenCoefficientRestriction R φ D ψ α hα X).map
          ((moduleAdj D ψ s).unit.app M) ≫ d.hom.app ((pull D ψ s).obj M) :=
    (unit_mateEquiv_symm (moduleAdj D ψ s) (moduleAdj R φ s) d.hom M).symm
  have ht := exactDerivedMate (moduleAdj D ψ s) (moduleAdj R φ s) d β hβ
  have hm : (mateEquiv a b).symm (Functor.mapDerivedCategorySquareIso d).hom =
      TwoSquare.mk _ _ _ _ (clopenCoefficientG R φ D ψ α hα s).hom := by
    apply TwoSquare.ext
    intro M
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm a b
      (Functor.mapDerivedCategorySquareIso d).hom M).symm.trans (ht M).symm
  have hi : IsIso (mateEquiv a b
      (clopenCoefficientG R φ D ψ α hα s).hom).natTrans := by
    change IsIso ((mateEquiv a b)
      (TwoSquare.mk _ _ _ _ (clopenCoefficientG R φ D ψ α hα s).hom)).natTrans
    rw [← hm, Equiv.apply_symm_apply]
    infer_instance
  exact mate_isIso_of_rightAdjoints (adj D ψ s) a (adj R φ s) b
    (clopenCoefficientG R φ D ψ α hα s).hom

/-- The coefficient/open mate is invertible on the whole system category.
Source: Stacks 03DI; proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: the ordinary extension comparison is identity on the selected component
and zero on its complement, and commutes with coefficient restriction. Localize
this exact comparison and its inverse. Its transpose is clopenCoefficientG inverse,
so adjunction uniqueness identifies it with the specified mate. -/
theorem clopenCoefficientJInv_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientJInv R φ D ψ α hα s) := by
  have := semilinearClopen_openUnit_isIso R φ s
  have := semilinearClopen_openUnit_isIso D ψ s
  have := clopenToDirect_isIso R φ s
  have := clopenToDirect_isIso D ψ s
  have := clopenCoefficientP_isIso R φ D ψ α hα s
  let ff := (jAdj R φ s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hi (M : Derived D ψ U) :
      IsIso ((clopenCoefficientJInv R φ D ψ α hα s).app M) := by
    let f := (clopenCoefficientJInv R φ D ψ α hα s).app M
    let e : (clopenCoefficientRes R φ D ψ α hα X).obj ((J D ψ s).obj M) ≅
        (J R φ s).obj ((clopenCoefficientRes R φ D ψ α hα U).obj M) :=
      (clopenCoefficientRes R φ D ψ α hα X).mapIso
          ((asIso (clopenToDirect D ψ s)).app M) ≪≫
        (asIso (clopenCoefficientP R φ D ψ α hα s)).app M ≪≫
        (asIso (clopenToDirect R φ s)).symm.app
          ((clopenCoefficientRes R φ D ψ α hα U).obj M)
    have := (jAdj R φ s).isIso_counit_app_of_iso e
    have := (jAdj R φ s).isIso_counit_app_of_iso
      (Iso.refl ((J R φ s).obj ((clopenCoefficientRes R φ D ψ α hα U).obj M)))
    have hg : IsIso ((G R φ s).map f) := by
      have hu := unit_mateEquiv_symm (jAdj D ψ s) (jAdj R φ s)
        (clopenCoefficientG R φ D ψ α hα s).inv M
      have : IsIso ((jAdj R φ s).unit.app
          ((clopenCoefficientRes R φ D ψ α hα U).obj M) ≫ (G R φ s).map f) := by
        change IsIso (_ ≫ (G R φ s).map
          (((mateEquiv (jAdj D ψ s) (jAdj R φ s)).symm
            (clopenCoefficientG R φ D ψ α hα s).inv).app M))
        dsimp only [Functor.id_obj] at hu
        rw [← hu]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((jAdj R φ s).unit.app ((clopenCoefficientRes R φ D ψ α hα U).obj M))
        ((G R φ s).map f)
    have h := (jAdj R φ s).counit.naturality f
    change (J R φ s).map ((G R φ s).map f) ≫ (jAdj R φ s).counit.app _ =
      (jAdj R φ s).counit.app _ ≫ f at h
    have : IsIso ((jAdj R φ s).counit.app _ ≫ f) := by
      rw [← h]
      change IsIso ((J R φ s).map ((G R φ s).map f) ≫
        (jAdj R φ s).counit.app
          ((clopenCoefficientRes R φ D ψ α hα X).obj ((J D ψ s).obj M)))
      exact IsIso.comp_isIso' (Functor.map_isIso (J R φ s) ((G R φ s).map f))
        ((jAdj R φ s).isIso_counit_app_of_iso e)
    exact IsIso.of_isIso_comp_left
      ((jAdj R φ s).counit.app
        ((J R φ s).obj ((clopenCoefficientRes R φ D ψ α hα U).obj M))) f
  exact NatIso.isIso_of_isIso_app _


/-- Orient the canonical coefficient/open comparison toward restricted coefficients.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientJ {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :=
  (@asIso _ _ _ _ (clopenCoefficientJInv R φ D ψ α hα s)
    (clopenCoefficientJInv_isIso R φ D ψ α hα s)).symm

/-- The three scalar-extension comparisons are the transposes of the actual
restriction comparisons under the normalized K-flat scalar adjunctions.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarG {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    G R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⋙ G D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction).symm
    (clopenCoefficientG R φ D ψ α hα s).hom

/-- Scalar extension of open extension, with its specified coefficient mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarJ {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    J R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⋙ J D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction).symm
    (clopenCoefficientJ R φ D ψ α hα s).inv

/-- Scalar extension of clopen direct image, with its specified coefficient mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarP {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    P R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⋙ P D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction).symm
    (@inv _ _ _ _ (clopenCoefficientP R φ D ψ α hα s)
      (clopenCoefficientP_isIso R φ D ψ α hα s))

private theorem inverseMate_iso_of_iterated
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : F₁ ⊣ U₁) (a₄ : F₂ ⊣ U₂)
    (d : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (mateEquiv a₄ a₃ d).natTrans] :
    IsIso ((mateEquiv a₁ a₂).symm d).natTrans := by
  let α := (mateEquiv a₁ a₂).symm d
  have h : IsIso (conjugateEquiv (a₁.comp a₄) (a₃.comp a₂) α.natTrans) := by
    rw [← iterated_mateEquiv_conjugateEquiv]
    dsimp only [α]
    rw [Equiv.apply_symm_apply]
    infer_instance
  exact conjugateEquiv_of_iso (a₁.comp a₄) (a₃.comp a₂) α.natTrans


private theorem inverseMate_interchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : F₁ ⊣ U₁) (a₄ : F₂ ⊣ U₂)
    (d : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (mateEquiv a₄ a₃ d).natTrans]
    [IsIso ((mateEquiv a₁ a₂).symm d).natTrans] :
    mateEquiv a₃ a₄
        (TwoSquare.mk _ _ _ _ (inv ((mateEquiv a₁ a₂).symm d).natTrans)) =
      (mateEquiv a₂ a₁).symm
        (TwoSquare.mk _ _ _ _ (inv (mateEquiv a₄ a₃ d).natTrans)) := by
  let α := (mateEquiv a₁ a₂).symm d
  let β := mateEquiv a₄ a₃ d
  have hi : conjugateIsoEquiv (a₁.comp a₄) (a₃.comp a₂) (asIso α.natTrans) =
      asIso β.natTrans := by
    apply Iso.ext
    change conjugateEquiv _ _ α.natTrans = β.natTrans
    rw [← iterated_mateEquiv_conjugateEquiv]
    dsimp only [α, β]
    rw [Equiv.apply_symm_apply]
  have h := congrArg Iso.inv hi
  change conjugateEquiv (a₃.comp a₂) (a₁.comp a₄) (inv α.natTrans) = inv β.natTrans at h
  apply (mateEquiv a₂ a₁).injective
  rw [Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro M
  exact congr_app ((iterated_mateEquiv_conjugateEquiv a₃ a₄ a₁ a₂ _).trans h) M

private theorem unit_mate_inverse
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D} {P' : D ⥤ C}
    (a : L ⊣ P) (b : L' ⊣ P') {E : A ⥤ C} {F : B ⥤ D}
    (j : L ⋙ F ⟶ E ⋙ L') [IsIso j] (g : P ⋙ E ⟶ F ⋙ P')
    (he : mateEquiv a b (TwoSquare.mk _ _ _ _ (inv j)) =
      TwoSquare.mk _ _ _ _ g) (N : A) :
    E.map (a.unit.app N) ≫ g.app (L.obj N) ≫ P'.map (j.app N) =
      b.unit.app (E.obj N) := by
  have h := unit_mateEquiv a b (TwoSquare.mk _ _ _ _ (inv j)) N
  rw [he] at h
  dsimp only [TwoSquare.mk, Functor.id_obj] at h
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  have hh := congr_app (IsIso.inv_hom_id j) N
  change (inv j).app N ≫ j.app N = 𝟙 _ at hh
  rw [hh]
  exact (congrArg (fun f ↦ b.unit.app _ ≫ f) (P'.map_id _)).trans (Category.comp_id _)

attribute [local irreducible] clopenCoefficientG

end Coefficients

attribute [local irreducible] clopenCoefficientScalar clopenCoefficientG

/-- The four explicit coefficient-naturality squares for the clopen maps and units.
This predicate introduces no operations: its arguments are the actual coefficient
functors and the canonical comparison words constructed above.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def ClopenCoefficientNaturality
    (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (EU : Derived R φ U ⥤ Derived D ψ U) (EX : Derived R φ X ⥤ Derived D ψ X)
    (g : G R φ s ⋙ EU ⟶ EX ⋙ G D ψ s)
    (j : J R φ s ⋙ EX ⟶ EU ⋙ J D ψ s)
    (p : P R φ s ⋙ EX ⟶ EU ⋙ P D ψ s) : Prop :=
  (∀ N : Derived R φ U,
    EX.map ((clopenToDirect R φ s).app N) ≫ p.app N =
      j.app N ≫ (clopenToDirect D ψ s).app (EU.obj N)) ∧
  (∀ M : Derived R φ X,
    EX.map ((clopenPi R φ s).app M) ≫ j.app ((G R φ s).obj M) ≫
        (J D ψ s).map (g.app M) = (clopenPi D ψ s).app (EX.obj M)) ∧
  (∀ N : Derived R φ U,
    EU.map ((jAdj R φ s).unit.app N) ≫ g.app ((J R φ s).obj N) ≫
        (G D ψ s).map (j.app N) = (jAdj D ψ s).unit.app (EU.obj N)) ∧
  (∀ M : Derived R φ X,
    EX.map ((adj R φ s).unit.app M) ≫ p.app ((G R φ s).obj M) ≫
        (P D ψ s).map (g.app M) = (adj D ψ s).unit.app (EX.obj M))

private theorem clopenNaturality_of_units
    (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (EU : Derived R φ U ⥤ Derived D ψ U) (EX : Derived R φ X ⥤ Derived D ψ X)
    (g : G R φ s ⋙ EU ⟶ EX ⋙ G D ψ s)
    (j : J R φ s ⋙ EX ⟶ EU ⋙ J D ψ s)
    (p : P R φ s ⋙ EX ⟶ EU ⋙ P D ψ s) [IsIso g]
    (hj : ∀ N, EU.map ((jAdj R φ s).unit.app N) ≫ g.app ((J R φ s).obj N) ≫
      (G D ψ s).map (j.app N) = (jAdj D ψ s).unit.app (EU.obj N))
    (hp : ∀ M, EX.map ((adj R φ s).unit.app M) ≫ p.app ((G R φ s).obj M) ≫
      (P D ψ s).map (g.app M) = (adj D ψ s).unit.app (EX.obj M)) :
    ClopenCoefficientNaturality R φ D ψ s EU EX g j p := by
  have := semilinearClopen_openUnit_isIso R φ s
  have := semilinearClopen_openUnit_isIso D ψ s
  have := clopenToDirect_isIso D ψ s
  have ht (N : Derived R φ U) :
      EX.map ((clopenToDirect R φ s).app N) ≫ p.app N =
        j.app N ≫ (clopenToDirect D ψ s).app (EU.obj N) := by
    have hk : (G D ψ s).map (j.app N) ≫ inv ((jAdj D ψ s).unit.app (EU.obj N)) =
        inv (g.app ((J R φ s).obj N)) ≫ EU.map (inv ((jAdj R φ s).unit.app N)) := by
      apply (cancel_epi (EU.map ((jAdj R φ s).unit.app N) ≫
        g.app ((J R φ s).obj N))).mp
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← EU.map_comp,
        IsIso.hom_inv_id, EU.map_id]
      rw [reassoc_of% (hj N), IsIso.hom_inv_id]
      rfl
    have hη : EX.map ((adj R φ s).unit.app ((J R φ s).obj N)) ≫
        p.app ((G R φ s).obj ((J R φ s).obj N)) =
      (adj D ψ s).unit.app (EX.obj ((J R φ s).obj N)) ≫
        (P D ψ s).map (inv (g.app ((J R φ s).obj N))) := by
      apply (cancel_mono ((P D ψ s).map (g.app ((J R φ s).obj N)))).mp
      simp only [Category.assoc]
      erw [← Functor.map_comp, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
      exact hp _
    rw [clopenToDirect_app, clopenToDirect_app]
    simp only [NatIso.isIso_inv_app]
    erw [Functor.map_comp, Category.assoc, p.naturality, ← Category.assoc, hη,
      Category.assoc, ← Functor.map_comp, ← hk, Functor.map_comp,
      ← Category.assoc, ← (adj D ψ s).unit.naturality]
    exact Category.assoc _ _ _
  refine ⟨ht, ?_, hj, hp⟩
  intro M
  apply (cancel_mono ((clopenToDirect D ψ s).app
    ((G D ψ s).obj (EX.obj M)))).mp
  have hπR := congr_app (clopenPi_toDirect R φ s) M
  have hπD := congr_app (clopenPi_toDirect D ψ s) (EX.obj M)
  change (clopenPi R φ s).app M ≫
    (clopenToDirect R φ s).app ((G R φ s).obj M) = (adj R φ s).unit.app M at hπR
  change (clopenPi D ψ s).app (EX.obj M) ≫
    (clopenToDirect D ψ s).app ((G D ψ s).obj (EX.obj M)) =
      (adj D ψ s).unit.app (EX.obj M) at hπD
  erw [hπD, Category.assoc, Category.assoc,
    (clopenToDirect D ψ s).naturality, ← reassoc_of% ht,
    ← Category.assoc, ← Functor.map_comp, hπR]
  exact hp M

/-- All clopen comparisons are natural for every compatible coefficient-system map,
both for exact restriction and for unbounded K-flat derived extension of scalars.
Source: Stacks 03DI and proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: restriction of scalars leaves the section pairs, inclusion (x,0) and
projection (x,y) to x unchanged. The identity-on-sections push comparison fixes
all three restriction comparisons by their adjunction transposes. Thus all four
squares commute already on ordinary systems and termwise complexes. Localize
them, using the exact/right-derived identification of clopen direct image.
For extension of scalars, the two clopen pieces identify systems with a product
of component categories. Balanced tensor maps, total tensor complexes, acyclicity
and K-flatness all split into the two components. Consequently the normalized
K-flat extension comparisons are invertible and are precisely the displayed
scalar-adjunction mates. Identity and zero commute with tensor on these actual
models. The four equations therefore descend from whole complexes of systems.
No flatness of α or of the transition maps, boundedness or cartesianness is used. -/
theorem semilinearClopen_coefficient_naturality
    (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    (α : ∀ n : ℕ, R n ⟶ D n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ ψ n = φ n ≫ α n)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    ClopenCoefficientNaturality D ψ R φ s
      (clopenCoefficientRes R φ D ψ α hα U) (clopenCoefficientRes R φ D ψ α hα X)
      (clopenCoefficientG R φ D ψ α hα s).inv
      (clopenCoefficientJ R φ D ψ α hα s).hom
      (clopenCoefficientP R φ D ψ α hα s) ∧
    IsIso (clopenScalarG R φ D ψ α hα s) ∧
    IsIso (clopenScalarJ R φ D ψ α hα s) ∧
    IsIso (clopenScalarP R φ D ψ α hα s) ∧
    ClopenCoefficientNaturality R φ D ψ s
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T
      (clopenCoefficientScalar R φ D ψ α hα X).scalar.T
      (clopenScalarG R φ D ψ α hα s)
      (clopenScalarJ R φ D ψ α hα s)
      (clopenScalarP R φ D ψ α hα s) := by
  have := semilinearClopen_openUnit_isIso R φ s
  have := semilinearClopen_openUnit_isIso D ψ s
  have := clopenCoefficientJInv_isIso R φ D ψ α hα s
  have := clopenCoefficientP_isIso R φ D ψ α hα s
  let rU := clopenCoefficientRes R φ D ψ α hα U
  let rX := clopenCoefficientRes R φ D ψ α hα X
  let g := clopenCoefficientG R φ D ψ α hα s
  let j := clopenCoefficientJ R φ D ψ α hα s
  let p := clopenCoefficientP R φ D ψ α hα s
  have hr : ClopenCoefficientNaturality D ψ R φ s rU rX g.inv j.hom p := by
    apply clopenNaturality_of_units D ψ R φ s rU rX g.inv j.hom p
    · intro N
      have h := unit_mateEquiv_symm (jAdj D ψ s) (jAdj R φ s)
        (TwoSquare.mk _ _ _ _ g.inv) N
      change rU.map ((jAdj D ψ s).unit.app N) ≫ g.inv.app _ =
        (jAdj R φ s).unit.app _ ≫ (G R φ s).map (j.inv.app N) at h
      erw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
        j.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
    · intro M
      have h := unit_mateEquiv (adj D ψ s) (adj R φ s)
        (TwoSquare.mk _ _ _ _ g.hom) M
      change rX.map ((adj D ψ s).unit.app M) ≫ p.app _ =
        (adj R φ s).unit.app _ ≫ (P R φ s).map (g.hom.app M) at h
      erw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
        g.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  let aU := (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction
  let aX := (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction
  have hpi : IsIso (mateEquiv (adj D ψ s) (adj R φ s)
      (TwoSquare.mk _ _ _ _ g.hom)).natTrans := by
    change IsIso (clopenCoefficientP R φ D ψ α hα s)
    exact clopenCoefficientP_isIso R φ D ψ α hα s
  have hg : IsIso (clopenScalarG R φ D ψ α hα s) := by
    exact inverseMate_iso_of_iterated aX aU (adj R φ s) (adj D ψ s)
      (TwoSquare.mk _ _ _ _ g.hom)
  have hji : mateEquiv (jAdj D ψ s) (jAdj R φ s)
      (TwoSquare.mk _ _ _ _ j.inv) = TwoSquare.mk _ _ _ _ g.inv := by
    change mateEquiv _ _ ((mateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have hjiIso : IsIso (mateEquiv (jAdj D ψ s) (jAdj R φ s)
      (TwoSquare.mk _ _ _ _ j.inv)).natTrans := by
    rw [hji]
    infer_instance
  have hj : IsIso (clopenScalarJ R φ D ψ α hα s) := by
    exact inverseMate_iso_of_iterated aU aX (jAdj R φ s) (jAdj D ψ s)
      (TwoSquare.mk _ _ _ _ j.inv)
  have hsj : IsIso ((mateEquiv aU aX).symm
      (TwoSquare.mk _ _ _ _ j.inv)).natTrans := hj
  have hsg : IsIso ((mateEquiv aX aU).symm
      (TwoSquare.mk _ _ _ _ g.hom)).natTrans := hg
  have hs : ClopenCoefficientNaturality R φ D ψ s
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T
      (clopenCoefficientScalar R φ D ψ α hα X).scalar.T
      (clopenScalarG R φ D ψ α hα s) (clopenScalarJ R φ D ψ α hα s)
      (clopenScalarP R φ D ψ α hα s) := by
    apply clopenNaturality_of_units R φ D ψ s
    · intro N
      have he : mateEquiv (jAdj R φ s) (jAdj D ψ s)
          (TwoSquare.mk _ _ _ _ (inv (clopenScalarJ R φ D ψ α hα s))) =
            TwoSquare.mk _ _ _ _ (clopenScalarG R φ D ψ α hα s) := by
        have h := inverseMate_interchange aU aX (jAdj R φ s) (jAdj D ψ s)
          (TwoSquare.mk _ _ _ _ j.inv)
        have hi : inv (mateEquiv (jAdj D ψ s) (jAdj R φ s)
            (TwoSquare.mk _ _ _ _ j.inv)).natTrans = g.hom := by
          apply IsIso.inv_eq_of_hom_inv_id
          rw [hji]
          exact g.inv_hom_id
        rw [hi] at h
        exact h
      exact unit_mate_inverse (jAdj R φ s) (jAdj D ψ s)
        (clopenScalarJ R φ D ψ α hα s) (clopenScalarG R φ D ψ α hα s) he N
    · intro M
      have he := inverseMate_interchange aX aU (adj R φ s) (adj D ψ s)
        (TwoSquare.mk _ _ _ _ g.hom)
      change mateEquiv (adj R φ s) (adj D ψ s)
        (TwoSquare.mk _ _ _ _ (inv (clopenScalarG R φ D ψ α hα s))) =
          TwoSquare.mk _ _ _ _ (clopenScalarP R φ D ψ α hα s) at he
      exact unit_mate_inverse (adj R φ s) (adj D ψ s)
        (clopenScalarG R φ D ψ α hα s) (clopenScalarP R φ D ψ α hα s) he M
  have hp : IsIso (clopenScalarP R φ D ψ α hα s) := by
    have := clopenToDirect_isIso R φ s
    have := clopenToDirect_isIso D ψ s
    have hi (N : Derived R φ U) : IsIso ((clopenCoefficientScalar R φ D ψ α hα X).scalar.T.map
        ((clopenToDirect R φ s).app N) ≫
        (clopenScalarP R φ D ψ α hα s).app N) := by
      rw [hs.1 N]
      infer_instance
    have hi' (N : Derived R φ U) : IsIso ((clopenScalarP R φ D ψ α hα s).app N) :=
      IsIso.of_isIso_comp_left
        ((clopenCoefficientScalar R φ D ψ α hα X).scalar.T.map
          ((clopenToDirect R φ s).app N)) _
    exact NatIso.isIso_of_isIso_app _
  exact ⟨hr, hg, hj, hp, hs⟩

end AlgebraicGeometry.ProEtale.VaryingRing
