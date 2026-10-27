module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Ordinary units and sections under site comparison

Source: Stacks Project, Tag 099R, section-comparison; current blueprint,
sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-a1-direct-image.proof.md, Step 4.
(blueprint: lem-pur-ordinary-unit-site-sections-transport).

The canonical finite-coefficient realization identifies fixed-scalar module sheaves
with modules over the finite coefficient ring sheaf. We use its fixed-scalar model,
as do the recorded counit-normalized mate and global comparison. Exact pullback on
D+ is the restriction of ordinary, uncompleted derived pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem terminal_sections_change
    {C A : Type*} [Category* C] [Category* A] (J : GrothendieckTopology C)
    [HasWeakSheafify J A] [HasTerminal C] {T S : C}
    (hT : IsTerminal T) (hS : IsTerminal S) (M : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).inv.app M ≫
      (Sheaf.ΓNatIsoSheafSections J A hS).hom.app M =
        M.obj.map (hT.from S).op := by
  have h : (Sheaf.ΓNatIsoSheafSections J A hS).hom =
      (Sheaf.ΓNatIsoSheafSections J A hT).hom ≫
        (Adjunction.rightAdjointUniq (constantSheafAdj J A hT)
          (constantSheafAdj J A hS)).hom := by
    symm
    exact Adjunction.rightAdjointUniq_trans _ _ _
  rw [h, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
  apply ((constantSheafAdj J A hS).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  apply ((sheafificationAdjunction J A).homEquiv _ _).injective
  have hs : ((constantSheafAdj J A hS).homEquiv _ _).symm
      (M.obj.map (hT.from S).op) =
      ((sheafificationAdjunction J A).homEquiv _ _).symm
        (((constantPresheafAdj A hS).homEquiv _ _).symm (M.obj.map (hT.from S).op)) := by
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    rfl
  erw [hs, Equiv.apply_symm_apply]
  have ht : ((sheafificationAdjunction J A).homEquiv _ _)
      ((constantSheafAdj J A hT).counit.app M) =
      (constantPresheafAdj A hT).counit.app M.obj := by
    apply ((constantPresheafAdj A hT).homEquiv _ _).injective
    have hc := congrFun (congrFun (Adjunction.comp_homEquiv
      (constantPresheafAdj A hT) (sheafificationAdjunction J A))
      (M.obj.obj (op T))) M
    have hc := Equiv.congr_fun hc ((constantSheafAdj J A hT).counit.app M)
    erw [← hc]
    dsimp only [constantSheafAdj]
    rw [← Adjunction.homEquiv_symm_id, ← Adjunction.homEquiv_symm_id]
    exact (Equiv.apply_symm_apply _ _).trans (Equiv.apply_symm_apply _ _).symm
  rw [ht]
  ext U
  change M.obj.map (hT.from U.unop).op =
    M.obj.map (hT.from S).op ≫ M.obj.map (hS.from U.unop).op
  rw [← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact hT.hom_ext _ _

private theorem exact_preserves_ge
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : DerivedCategory.Plus C) (n : ℤ) [M.IsGE n] :
    (F.mapDerivedCategoryPlus.obj M).IsGE n := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  exact IsZero.of_iso (F.map_isZero (DerivedCategory.Plus.isZero_homology_of_isGE M n i hi))
    ((F.mapDerivedCategoryPlusHomologyFunctorIso i).app M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_of_counit
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {l : C ⥤ D} {r : D ⥤ C} {p : E ⥤ F} {t : F ⥤ E}
    {a : C ⥤ E} {b : D ⥤ F} (e : l ⊣ r) (d : p ⊣ t)
    (α : l ⋙ b ≅ a ⋙ p) (β : r ⋙ a ⟶ b ⋙ t)
    (h : ∀ K, α.hom.app (r.obj K) ≫ p.map (β.app K) ≫
      d.counit.app (b.obj K) = b.map (e.counit.app K)) (M : C) :
    d.unit.app (a.obj M) = a.map (e.unit.app M) ≫ β.app (l.obj M) ≫
      t.map (α.hom.app M) := by
  have hβ : β = (mateEquiv e d α.inv).natTrans := by
    apply NatTrans.ext
    funext K
    apply (d.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    rw [mateEquiv_counit]
    apply (cancel_epi (α.hom.app (r.obj K))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h K
  rw [hβ, ← Category.assoc, unit_mateEquiv]
  rw [Category.assoc, ← t.map_comp]
  change d.unit.app (a.obj M) = d.unit.app (a.obj M) ≫
    t.map (α.inv.app M ≫ α.hom.app M)
  rw [Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm.trans
    (congrArg (fun z ↦ d.unit.app (a.obj M) ≫ z) (t.map_id _).symm)

section OrdinaryDerivedNormalization

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {G : C ⥤ E} {H : D ⥤ E}
  [L.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private noncomputable def normalizedBaseChange (e : G ⟶ L ⋙ H) :
    G.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := G) (G' := H) (β := L) (γ := 𝟭 E) ((Functor.rightUnitor G).hom ≫ e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private lemma normalizedBaseChange_fac (e : G ⟶ L ⋙ H) (K : HomotopyCategory.Plus C) :
    G.rightDerivedFunctorPlusUnit.app K ≫
      (normalizedBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
      H.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [normalizedBaseChange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Functor.rightUnitor_inv_app, Category.id_comp]
  have hi := (Functor.mapDerivedCategoryPlusIdIso E).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.id_map] at hi
  rw [reassoc_of% hi]
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (G := G) (G' := H) (β := L) (γ := 𝟭 E)
    ((Functor.rightUnitor G).hom ≫ e)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hfac
  rw [hfac]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  simp only [Iso.inv_hom_id_app_assoc]
  have hu : (Functor.rightUnitor G).hom ≫ e = e := by
    ext X
    exact Category.id_comp _
  rw [hu]
  erw [Category.id_comp, Category.id_comp]

private theorem normalized_right_unitor (e : G ⋙ 𝟭 E ⟶ L ⋙ H) :
    normalizedBaseChange ((Functor.rightUnitor G).inv ≫ e) =
      (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E).inv ≫
        Functor.rightDerivedFunctorPlusBaseChange e := by
  have he : (Functor.rightUnitor G).hom ≫ (Functor.rightUnitor G).inv ≫ e = e := by
    simp
  simp only [normalizedBaseChange, he, Functor.isoWhiskerLeft_inv]

variable (R : D ⥤ C) [R.Additive] [R.PreservesInjectiveObjects] (adj : L ⊣ R)

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesInjectiveObjects] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem liftedUnit (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus
      (Functor.whiskerRight adj.unit G)).app K =
    G.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.unit.app K) := by
  apply (HomotopyCategory.Plus.ι E).map_injective
  change (NatTrans.mapHomotopyCategory
      (Functor.whiskerRight adj.unit G)
      (ComplexShape.up ℤ)).app K.obj =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K))
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  have hη (Y : HomotopyCategory C (ComplexShape.up ℤ)) :
      (NatTrans.mapHomotopyCategory
        (Functor.whiskerRight adj.unit G)
        (ComplexShape.up ℤ)).app Y =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app Y) := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
    congr 1
  exact hη K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem supportBaseChange_unit :
    normalizedBaseChange (G := G) (L := L) (H := R ⋙ G) (Functor.whiskerRight adj.unit G) ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso R G).hom =
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, normalizedBaseChange_fac]
  simp only [Category.assoc]
  erw [(Functor.rightDerivedFunctorPlusCompIso R G).hom.naturality]
  rw [Functor.rightDerivedFunctorPlusCompIso_fac_app_assoc,
    Functor.rightDerivedFunctorPlusCompUnit_app]
  rw [liftedUnit]
  have hn := G.rightDerivedFunctorPlusUnit.naturality
    (adj.mapHomotopyCategoryPlus.unit.app K)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn]
  simp only [Functor.comp_map]
  rw [← G.rightDerivedFunctorPlus.map_comp_assoc,
    ← G.rightDerivedFunctorPlus.map_comp]
  rw [← adj.derivedPlus_unit_app_fac]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem normalizedBaseChange_naturality
    {G₂ : C ⥤ E} {H₂ : D ⥤ E} [G₂.Additive] [H₂.Additive]
    (e : G ⟶ L ⋙ H) (e₂ : G₂ ⟶ L ⋙ H₂) (a : G ⟶ G₂) (b : H ⟶ H₂)
    (h : e ≫ Functor.whiskerLeft L b = a ≫ e₂) :
    normalizedBaseChange e ≫
        Functor.whiskerLeft L.mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusNatTrans b) =
      Functor.rightDerivedFunctorPlusNatTrans a ≫ normalizedBaseChange e₂ := by
  refine Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, normalizedBaseChange_fac]
  simp only [Category.assoc]
  erw [(Functor.rightDerivedFunctorPlusNatTrans b).naturality]
  rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  erw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc, normalizedBaseChange_fac]
  have hh := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h) K
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
  have heq : (NatTrans.mapHomotopyCategoryPlus e).app K ≫
        (NatTrans.mapHomotopyCategoryPlus b).app (L.mapHomotopyCategoryPlus.obj K) =
      (NatTrans.mapHomotopyCategoryPlus a).app K ≫
        (NatTrans.mapHomotopyCategoryPlus e₂).app K := hh
  erw [← DerivedCategory.Plus.Qh.map_comp_assoc,
    heq, CategoryTheory.Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem section_unit_leray (e : R ⋙ G ≅ H) :
    normalizedBaseChange (G := G) ((Functor.leftUnitor G).inv ≫
      Functor.whiskerRight adj.unit G ≫
      (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom) =
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso' R G e).hom := by
  have hn := normalizedBaseChange_naturality
    (L := L) (G := G) (H := R ⋙ G) (H₂ := H)
    (Functor.whiskerRight adj.unit G)
    (Functor.whiskerRight adj.unit G ≫
      (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom)
    (𝟙 G) e.hom (by ext X; simp)
  have hid : Functor.rightDerivedFunctorPlusNatTrans (𝟙 G) = 𝟙 _ := by
    simp [Functor.rightDerivedFunctorPlusNatTrans]
  rw [hid, Category.id_comp] at hn
  have he : (Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
      (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom =
    Functor.whiskerRight adj.unit G ≫
      (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom := by
    ext M
    simp
  rw [he, ← hn]
  have hu := supportBaseChange_unit (G := G) R adj
  rw [← hu]
  ext M : 2
  simp [Functor.rightDerivedFunctorPlusCompIso',
    Functor.rightDerivedFunctorPlusNatIso, Category.assoc]

end OrdinaryDerivedNormalization

section OrdinaryPasting

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory F] [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives F]
  {G : C ⥤ E} {H : D ⥤ E} {I : F ⥤ E} {L : C ⥤ D} {P : D ⥤ F}
  [G.Additive] [H.Additive] [I.Additive] [L.Additive] [P.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem normalized_pasting (e : G ⟶ L ⋙ H) (e' : H ⟶ P ⋙ I)
    (M : DerivedCategory.Plus C) :
    (normalizedBaseChange e).app M ≫
        (normalizedBaseChange e').app (L.mapDerivedCategoryPlus.obj M) =
      (normalizedBaseChange (L := L ⋙ P) (H := I) (e ≫ Functor.whiskerLeft L e')).app M ≫
        I.rightDerivedFunctorPlus.map ((Functor.mapDerivedCategoryPlusCompIso L P).hom.app M) := by
  suffices hn : normalizedBaseChange e ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus (normalizedBaseChange e') =
    normalizedBaseChange (L := L ⋙ P) (H := I) (e ≫ Functor.whiskerLeft L e') ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIso L P).hom
        I.rightDerivedFunctorPlus from congr_app hn M
  apply Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, normalizedBaseChange_fac]
  have hn := (normalizedBaseChange e').naturality (L.mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [hn]
  erw [reassoc_of% (normalizedBaseChange_fac e' (L.mapHomotopyCategoryPlus.obj K))]
  rw [reassoc_of% (normalizedBaseChange_fac (L := L ⋙ P) (H := I)
    (e ≫ Functor.whiskerLeft L e') K)]
  have hc : (L ⋙ P).mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (Functor.mapDerivedCategoryPlusCompIso L P).hom.app (DerivedCategory.Plus.Qh.obj K) =
    P.mapDerivedCategoryPlusFactorsh.inv.app (L.mapHomotopyCategoryPlus.obj K) ≫
      P.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    have h := Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh L P K
    rw [← cancel_epi ((L ⋙ P).mapDerivedCategoryPlusFactorsh.hom.app K)]
    simp only [Iso.hom_inv_id_app_assoc]
    simp only [← h, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have he : (NatTrans.mapHomotopyCategoryPlus (e ≫ Functor.whiskerLeft L e')).app K =
      (NatTrans.mapHomotopyCategoryPlus e).app K ≫
        (NatTrans.mapHomotopyCategoryPlus e').app (L.mapHomotopyCategoryPlus.obj K) := by
    have h : (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft L e')).app K =
        (NatTrans.mapHomotopyCategoryPlus e').app (L.mapHomotopyCategoryPlus.obj K) := rfl
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app, h]
  have hm := congrArg I.rightDerivedFunctorPlus.map hc
  simp only [CategoryTheory.Functor.map_comp] at hm
  erw [← hm]
  rw [he, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem normalized_iso
    {P' : C ⥤ F} [P'.Additive] [PreservesFiniteLimits P']
    [PreservesFiniteColimits P'] {L' : C ⥤ F} [L'.Additive]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (e : G ⟶ P' ⋙ I) (e' : G ⟶ L' ⋙ I) (α : P' ≅ L')
    (h : e ≫ Functor.whiskerRight α.hom I = e') (M : DerivedCategory.Plus C) :
    (normalizedBaseChange e).app M ≫
        I.rightDerivedFunctorPlus.map ((Functor.mapDerivedCategoryPlusNatIso α).hom.app M) =
      (normalizedBaseChange e').app M := by
  suffices hn : normalizedBaseChange e ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryPlusNatIso α).hom
        I.rightDerivedFunctorPlus = normalizedBaseChange e' from congr_app hn M
  apply Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, normalizedBaseChange_fac, normalizedBaseChange_fac]
  have hv : P'.mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (Functor.mapDerivedCategoryPlusNatIso α).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus α.hom).app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.inv.app K := by
    rw [← cancel_epi (P'.mapDerivedCategoryPlusFactorsh.hom.app K),
      ← cancel_mono (L'.mapDerivedCategoryPlusFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    exact (Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh α K).trans
      (by erw [Category.comp_id])
  have hh := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h) K
  have hw : (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight α.hom I)).app K =
      I.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus α.hom).app K) := rfl
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app, hw] at hh
  have hn := I.rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapHomotopyCategoryPlus α.hom).app K)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [← I.rightDerivedFunctorPlus.map_comp, hv]
  rw [CategoryTheory.Functor.map_comp]
  erw [← reassoc_of% hn, ← DerivedCategory.Plus.Qh.map_comp_assoc, hh]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem normalized_square
    {D' : Type*} [Category* D'] [Abelian D'] [HasDerivedCategory D']
    [EnoughInjectives D'] {H' : D' ⥤ E} {L' : C ⥤ D'} {P' : D' ⥤ F}
    [H'.Additive] [L'.Additive] [P'.Additive]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (e : G ⟶ L ⋙ H) (e' : H ⟶ P ⋙ I)
    (a : G ⟶ L' ⋙ H') (a' : H' ⟶ P' ⋙ I)
    (α : L' ⋙ P' ≅ L ⋙ P)
    (h : (a ≫ Functor.whiskerLeft L' a') ≫ Functor.whiskerRight α.hom I =
      e ≫ Functor.whiskerLeft L e') (M : DerivedCategory.Plus C) :
    (normalizedBaseChange e).app M ≫
        (normalizedBaseChange e').app (L.mapDerivedCategoryPlus.obj M) =
      (normalizedBaseChange a).app M ≫
        (normalizedBaseChange a').app (L'.mapDerivedCategoryPlus.obj M) ≫
        I.rightDerivedFunctorPlus.map
          (((Functor.mapDerivedCategoryPlusCompIso L' P').inv ≫
            (Functor.mapDerivedCategoryPlusNatIso α).hom ≫
            (Functor.mapDerivedCategoryPlusCompIso L P).hom).app M) := by
  rw [normalized_pasting e e' M, ← Category.assoc, normalized_pasting a a' M]
  have hi := normalized_iso (I := I)
    (a ≫ Functor.whiskerLeft L' a') (e ≫ Functor.whiskerLeft L e') α h M
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← I.rightDerivedFunctorPlus.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, hi]

end OrdinaryPasting



namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The canonical terminal-evaluation identification for direct image.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryEtaleTerminalIso {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))) ≅
      sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.Etale.isTerminalMkId X)).symm ≪≫
    Etale.lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f ≪≫
    Sheaf.ΓNatIsoSheafSections _ _ (Scheme.Etale.isTerminalMkId Y)

/-- Canonical Leray isomorphism for ordinary derived terminal sections.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryEtaleLeray {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  @Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))) _ _ _ _
    (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    (ordinaryEtaleTerminalIso Λ f)

/-- The ordinary section pullback, given by the sheaf adjunction unit and terminal base change.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryEtaleSectionUnit {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))) ⋙ 𝟭 (ModuleCat.{u + 1} Λ) ⟶
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ (sheafToPresheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 Y)))) :=
  (Functor.rightUnitor _).hom ≫
    (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (ordinaryEtaleTerminalIso Λ f).hom

/-- Derive the ordinary section pullback. Its cohomology is the usual resolution pullback:
apply the section-unit map termwise to an injective resolution, then a comparison
into a resolution of its inverse image, and take cohomology. This construction is
normalized by rightDerivedFunctorPlusBaseChange_fac, with classical nonnegative
cohomology identified by rightDerivedBaseChange_app.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryEtaleSectionPullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerivedFunctorPlus ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 Y)))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange (ordinaryEtaleSectionUnit Λ f)

/-- The canonical terminal-evaluation identification for direct image.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryProEtaleTerminalIso {Y X : Scheme.{u}} (f : Y ⟶ X) :
    lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (sheafToPresheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))) ≅
      sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y))) :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm ≪≫
    globalSectionsLowerStarIso (ModuleCat.{u + 1} Λ) f ≪≫
    Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Y)

/-- Canonical Leray isomorphism for ordinary derived terminal sections.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryProEtaleLeray {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  @Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (lowerStar (ModuleCat.{u + 1} Λ) f) (sheafToPresheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))) _ _ _ _
    (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    (ordinaryProEtaleTerminalIso Λ f)

/-- The ordinary section pullback, given by the sheaf adjunction unit and terminal base change.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryProEtaleSectionUnit {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))) ⋙ 𝟭 (ModuleCat.{u + 1} Λ) ⟶
      upperStar (ModuleCat.{u + 1} Λ) f ⋙ (sheafToPresheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y)))) :=
  (Functor.rightUnitor _).hom ≫
    (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (ordinaryProEtaleTerminalIso Λ f).hom

/-- Derive the ordinary section pullback. Its cohomology is the usual resolution pullback:
apply the section-unit map termwise to an injective resolution, then a comparison
into a resolution of its inverse image, and take cohomology. This construction is
normalized by rightDerivedFunctorPlusBaseChange_fac, with classical nonnegative
cohomology identified by rightDerivedBaseChange_app.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinaryProEtaleSectionPullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y)))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange (ordinaryProEtaleSectionUnit Λ f)

/-- The recorded global site comparison, with the canonical derived-identity
isomorphism inserted at its source. This changes only the presentation of the
source functor, and retains finiteComparisonGlobalSections itself as the arrow.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
def ordinarySiteGlobalComparison (T : Scheme.{u}) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv ≫
    finiteComparisonGlobalSections T Λ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_terminal_app {Y X : Scheme.{u}} (f : Y ⟶ X)
    (K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (ordinaryEtaleTerminalIso Λ f).hom.app K =
      K.obj.map (((Scheme.Etale.isTerminalMkId X).isTerminalObj f.Etale _).from
        (Scheme.Etale.mk (𝟙 Y))).op := by
  simp only [ordinaryEtaleTerminalIso, Etale.lowerStarCompGlobalSectionsIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% terminal_sections_change _ (Scheme.Etale.isTerminalMkId X)
    terminalIsTerminal _]
  rw [terminal_sections_change _ terminalIsTerminal (Scheme.Etale.isTerminalMkId Y) _]
  change K.obj.map _ ≫ K.obj.map _ ≫ K.obj.map _ = _
  rw [← K.obj.map_comp, ← K.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact ((Scheme.Etale.isTerminalMkId X).isTerminalObj f.Etale _).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem proetale_terminal_app {Y X : Scheme.{u}} (f : Y ⟶ X)
    (K : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    (ordinaryProEtaleTerminalIso Λ f).hom.app K =
      K.obj.map (overPullbackObjMkIdIso f).inv.op := by
  simp [ordinaryProEtaleTerminalIso, globalSectionsLowerStarIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem sheaf_composite_unit {Y X : Scheme.{u}} (f : Y ⟶ X)
    (K : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app K ≫
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj K)) =
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).map
        ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj K)) ≫
      (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj K)) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map
        ((lowerStar (ModuleCat.{u + 1} Λ) f).map
          ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app K)) := by
  have h := unit_conjugateEquiv_symm
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y))
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv K
  change _ = _ ≫ (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map
    ((lowerStar (ModuleCat.{u + 1} Λ) f).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app K)) at h
  have ht := congrArg (fun z ↦ z ≫
    (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map
      ((lowerStar (ModuleCat.{u + 1} Λ) f).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app K))) h
  simp only [Adjunction.comp_unit_app, Category.assoc] at ht
  rw [← (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map_comp,
    ← (lowerStar (ModuleCat.{u + 1} Λ) f).map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at ht
  exact ht.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem ordinary_sections_square {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Functor.rightUnitor _).inv ≫ finiteComparisonGlobalSectionsUnit X Λ ≫
      Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        ((Functor.rightUnitor _).inv ≫ ordinaryProEtaleSectionUnit Λ f) =
    (Functor.rightUnitor _).inv ≫ ordinaryEtaleSectionUnit Λ f ≫
      Functor.whiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        ((Functor.rightUnitor _).inv ≫ finiteComparisonGlobalSectionsUnit Y Λ) ≫
      Functor.whiskerRight
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv
        (sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
          (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y)))) := by
  ext K : 2
  have h := sheaf_composite_unit Λ f K
  have h := congrArg (fun z ↦ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).map z |>.app (op (Scheme.Etale.mk (𝟙 X)))) h
  simp only [ordinaryEtaleSectionUnit, ordinaryProEtaleSectionUnit,
    finiteComparisonGlobalSectionsUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    etale_terminal_app, proetale_terminal_app]
  dsimp only [Functor.comp_map, sheafToPresheaf, NatTrans.comp_app] at h
  simp only [Functor.comp_map, Category.assoc]
  erw [reassoc_of% h]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    Category.assoc]
  have hn := NatTrans.naturality
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app K).hom
    (overPullbackObjMkIdIso f).inv.op
  erw [← hn]
  erw [Category.id_comp]
  congr 1
  have hr : ((lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj K))).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) = 𝟙 _ := by
    change _ = 𝟙 _
    simp only [Functor.comp_obj, lowerStarCompComparisonLowerStarIso,
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, toProEtCompOverPullbackIso,
      ObjectProperty.ι_obj, Iso.refl_symm, Iso.trans_inv, Iso.refl_inv, Category.assoc,
      NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, Functor.sheafPushforwardContinuous_obj_obj_obj,
      Functor.whiskerRight_app, Functor.op_obj, NatTrans.op_app,
      NatIso.ofComponents_hom_app, Iso.refl_hom, op_id, Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  erw [hr, Category.id_comp]
  have hu := ((comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj K)).hom.naturality
      (((Scheme.Etale.isTerminalMkId X).isTerminalObj f.Etale _).from
        (Scheme.Etale.mk (𝟙 Y))).op
  have ha : (Y.toProEt.map
      (((Scheme.Etale.isTerminalMkId X).isTerminalObj f.Etale _).from
        (Scheme.Etale.mk (𝟙 Y)))).op = (overPullbackObjMkIdIso f).inv.op := by
    apply Quiver.Hom.unop_inj
    exact ((Scheme.ProEt.isTerminalMkId X).isTerminalObj
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) _).hom_ext _ _
  erw [← ha, ← reassoc_of% hu]
  rfl

variable [hfinite : Finite Λ] {Y X : Scheme.{u}} (f : Y ⟶ X)
  [hqc : QuasiCompact f] [hqs : QuasiSeparated f]
  (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

include hfinite hqc hqs

/-- The actual derived units satisfy the canonical mate equation.

Proof: transpose the right-hand composite under pro-etale pullback/direct image.
The counit normalization of lem-weil-pbc-comparison-direct-image-canonical-mate
reduces its transpose to the etale counit composed with the pulled-back etale unit,
conjugated by the pullback comparison. Naturality and the etale triangle identity
make this the identity. The transpose of the pro-etale unit is also the identity,
and the adjunction bijection is injective (def-weil-pbc-adjunction-mate).
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
theorem ordinaryUnitSiteTransport :
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ≫
      (fixedComparisonDirectImageMatePlus Λ f).app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus Λ f).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) := by
  exact unit_of_counit
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f)
    (fixedComparisonPullbackPlus Λ f) (fixedComparisonDirectImageMatePlus Λ f)
    (fixedComparisonDirectImageMatePlus_counit Λ f) _

set_option maxRecDepth 3000 in
set_option linter.unusedSectionVars false in
/-- The two ordinary pullbacks are the same under the named global comparisons
and the canonical pullback comparison; no invertibility of the etale unit is assumed.

Proof: apply the composition and geometric-2-isomorphism equations of
lem-pur-site-derived-sections-unit-pasting to the two composites of f with nu.
Their inverse-image comparison is fixedComparisonPullbackPlus. The coefficient
identifications preserve constants by prop-weil-pbc-proetale-constant-ring-map.
The nu section maps are exactly finiteComparisonGlobalSections by
lem-weil-pbc-comparison-global-cohomology. Substitution gives this equality.
Every factor is a natural transformation, so the identity is natural in L.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
theorem ordinaryUnitSiteSections_comparison :
    (ordinarySiteGlobalComparison Λ X).app ((DerivedCategory.Plus.singleFunctor _ 0).obj L) ≫
        (ordinaryProEtaleSectionPullback Λ f).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) =
      (ordinaryEtaleSectionPullback Λ f).app ((DerivedCategory.Plus.singleFunctor _ 0).obj L) ≫
        (ordinarySiteGlobalComparison Λ Y).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ≫
        (sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y)))).rightDerivedFunctorPlus.map
          ((fixedComparisonPullbackPlus Λ f).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) := by
  have h := normalized_square
    (H := sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X))))
    ((Functor.rightUnitor _).inv ≫ finiteComparisonGlobalSectionsUnit X Λ)
    ((Functor.rightUnitor _).inv ≫ ordinaryProEtaleSectionUnit Λ f)
    ((Functor.rightUnitor _).inv ≫ ordinaryEtaleSectionUnit Λ f)
    ((Functor.rightUnitor _).inv ≫ finiteComparisonGlobalSectionsUnit Y Λ)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    (ordinary_sections_square Λ f).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj L)
  simpa only [normalized_right_unitor, ordinarySiteGlobalComparison,
    finiteComparisonGlobalSections,
    ordinaryProEtaleSectionPullback, ordinaryEtaleSectionPullback,
    fixedComparisonPullbackPlus, Iso.trans_hom, Iso.symm_hom, Scheme.toProEt] using h

set_option maxRecDepth 3000 in
set_option linter.unusedSectionVars false in
/-- Ordinary section pullback is derived sections of the actual unit followed by Leray.

Proof: apply lem-pur-site-derived-sections-unit-pasting separately on the two sites.
The constant-ring identifications are those preserving constant sections, as in
prop-weil-pbc-proetale-constant-ring-map. On injective resolutions, both sides
are the ordinary section pullback followed by the comparison into an inverse-image
resolution. The defining unit compatibility of the derived comparison and Leray
identifies these maps, and uniqueness of right-derived transformations proves equality.
Taking homology in any integer degree identifies the induced maps with the usual
cohomology pullbacks; rightDerivedBaseChange_app gives the classical nonnegative form.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
theorem ordinaryUnitSiteSections_unit_leray :
    (ordinaryEtaleSectionPullback Λ f).app ((DerivedCategory.Plus.singleFunctor _ 0).obj L) =
        (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerivedFunctorPlus.map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ≫
        (ordinaryEtaleLeray Λ f).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ∧
      (ordinaryProEtaleSectionPullback Λ f).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) =
        (sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))).rightDerivedFunctorPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) ≫
        (ordinaryProEtaleLeray Λ f).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) := by
  have : (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  have : (lowerStar (ModuleCat.{u + 1} Λ) f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  constructor
  · have h := congr_app (section_unit_leray
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (ordinaryEtaleTerminalIso Λ f)) ((DerivedCategory.Plus.singleFunctor _ 0).obj L)
    simpa only [ordinaryEtaleSectionPullback, ordinaryEtaleSectionUnit,
      normalizedBaseChange, ordinaryEtaleLeray,
      Etale.derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_inv, Category.id_comp,
      Category.comp_id] using h
  · have h := congr_app (section_unit_leray
      (lowerStar (ModuleCat.{u + 1} Λ) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (ordinaryProEtaleTerminalIso Λ f))
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj L))
    simpa only [ordinaryProEtaleSectionPullback, ordinaryProEtaleSectionUnit,
      normalizedBaseChange, ordinaryProEtaleLeray,
      derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_inv, Category.id_comp,
      Category.comp_id] using h

/-- An invertible etale unit gives the actual invertible pro-etale unit and
invertible ordinary section pullbacks on both sites.

Proof: the mate is invertible on the degree-zero inverse image by
lem-weil-pbc-comparison-direct-image-canonical-mate, and the pullback comparison
is an isomorphism. The unit equation therefore makes the pro-etale unit invertible.
By lem-pur-site-derived-sections-unit-pasting, each ordinary section pullback
is sections of its derived unit followed by the canonical Leray isomorphism.
Functors preserve isomorphisms, so both section pullbacks are invertible.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
theorem ordinaryUnitSiteTransport_isIso
    (h : IsIso ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) ∧
      IsIso ((ordinaryEtaleSectionPullback Λ f).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) ∧
      IsIso ((ordinaryProEtaleSectionPullback Λ f).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) := by
  let := h
  have := isIso_fixedComparisonDirectImageMatePlus Λ f
  have hp : IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj L))) := by
    rw [ordinaryUnitSiteTransport Λ f L]
    infer_instance
  obtain ⟨he, ht⟩ := ordinaryUnitSiteSections_unit_leray Λ f L
  refine ⟨hp, ?_, ?_⟩
  · rw [he]
    infer_instance
  · rw [ht]
    infer_instance

set_option linter.unusedSectionVars false in
/-- The four ordinary section complexes in the comparison square have zero
negative cohomology, covering all integer degrees in the cohomology assertion.

Proof: the sheaf L is in degree zero. Exact etale pullback and exact site comparison
retain this lower bound, as does exact pro-etale pullback. Right-derived terminal
sections are left t-exact, computed by resolutions supported in nonnegative degrees.
Thus each of their homology objects in a negative degree is zero. This is the
negative-degree clause of lem-pur-site-derived-sections-unit-pasting on both sites.
Source: Stacks Tag 099R and blueprint transport Step 4
(blueprint: lem-pur-ordinary-unit-site-sections-transport). -/
theorem ordinaryUnitSiteSections_negative (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerivedFunctorPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj L)))) ∧
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 Y)))).rightDerivedFunctorPlus.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)))) ∧
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj L)))) ∧
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 Y)))).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj L))))) := by
  have he := exact_preserves_ge (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj L) 0
  have hc := exact_preserves_ge (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj L) 0
  have hp := exact_preserves_ge (upperStar (ModuleCat.{u + 1} Λ) f)
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj L)) 0
  exact ⟨Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq,
    Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq,
    Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq,
    Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq⟩

end AlgebraicGeometry.ProEtale
