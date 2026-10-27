/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.EtaleProEtaleGraphSheafSquare
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

/-! # Derived mate factorization of compactified graph comparison

Source: Stacks Project, derived.tex, Tags 0FND and 015F; proetale.tex, Tag 09AF
(blueprint: lem-sp-graph-derived-mate-factorization).

The categorical helper expressions display all localization identifications. They are
instantiated below with the fixed geometric functors and their specified maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe a av b bv c cv d dv u wB wC wD wE wB' wC' wD'
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem graphMate_whiskerRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F F' : C ⥤ D} [F.Additive] [F'.Additive] (t : F ⟶ F')
    (H : D ⥤ E) [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight t H)).app K =
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus t).app K) := by
  have h := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app t H K
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

private theorem graphMate_whiskerLeft
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) [F.Additive] {H H' : D ⥤ E} [H.Additive] [H'.Additive]
    (t : H ⟶ H') (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F t)).app K =
      (NatTrans.mapHomotopyCategoryPlus t).app (F.mapHomotopyCategoryPlus.obj K) := by
  have h := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app F t K
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

section ExactSquare
variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  (H : C ⥤ D) (I : D ⥤ F) (J : C ⥤ E) (K : E ⥤ F)
  [H.Additive] [I.Additive] [J.Additive] [K.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

private theorem graphMate_iso_factors (t : H ⋙ I ≅ J ⋙ K)
    (P : HomotopyCategory.Plus C) :
    ((Functor.mapDerivedCategoryPlusCompIso H I).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso t ≪≫
        Functor.mapDerivedCategoryPlusCompIso J K).hom.app (DerivedCategory.Plus.Qh.obj P) ≫
      K.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app P) ≫
      K.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj P) =
    I.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app P) ≫
      I.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj P) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t.hom).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh J K P]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh t P]
  rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh H I P]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

end ExactSquare

section Categorical
variable {C : Type a} [Category.{av} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {C' : Type c} [Category.{cv} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  {D' : Type d} [Category.{dv} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  [EnoughInjectives D] [EnoughInjectives D']
  (l : C ⥤ D) (r : D ⥤ C) (L : C' ⥤ D') (R : D' ⥤ C')
  (V : D ⥤ D') (W : C ⥤ C')
  [l.Additive] [r.Additive] [L.Additive] [R.Additive] [V.Additive] [W.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]

/-- The ordinary comparison after passing to bounded below homotopy categories.
Source: Stacks Tag 0FND (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateHomotopyComparison (δ : r ⋙ W ⟶ V ⋙ R) :
    r.mapHomotopyCategoryPlus ⋙ W.mapHomotopyCategoryPlus ⟶
      V.mapHomotopyCategoryPlus ⋙ R.mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (r ⋙ W))).hom ≫
    NatTrans.mapHomotopyCategoryPlus δ ≫
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (V ⋙ R))).inv

/-- `W(gamma_et) b`, naturally on representatives.
Source: Stacks Tag 0FND (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateLeft
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) :
    r.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ W.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
  Functor.whiskerRight r.rightDerivedFunctorPlusUnit W.mapDerivedCategoryPlus ≫
    Functor.whiskerLeft DerivedCategory.Plus.Qh β

/-- `Q(d) gamma_proet`, naturally on representatives, with exact-functor factors.
Source: Stacks Tags 0FND and 015F (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateRight (δ : r ⋙ W ⟶ V ⋙ R) :
    r.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ W.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
  Functor.whiskerLeft r.mapHomotopyCategoryPlus W.mapDerivedCategoryPlusFactorsh.hom ≫
    Functor.whiskerRight (graphMateHomotopyComparison r R V W δ) DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft V.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight V.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus

/-- The etale description `a^(-1) VQ(epsilon_et^0)` of the common transpose.
Source: Stacks Tag 0FND (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateEtaleCounitExpression (adj : l ⊣ r)
    (α : l.mapDerivedCategoryPlus ⋙ V.mapDerivedCategoryPlus ≅
      W.mapDerivedCategoryPlus ⋙ L.mapDerivedCategoryPlus) (P : HomotopyCategory.Plus D) :
    L.mapDerivedCategoryPlus.obj (W.mapDerivedCategoryPlus.obj
        (DerivedCategory.Plus.Qh.obj (r.mapHomotopyCategoryPlus.obj P))) ⟶
      V.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj P) :=
  α.inv.app (DerivedCategory.Plus.Qh.obj (r.mapHomotopyCategoryPlus.obj P)) ≫
    V.mapDerivedCategoryPlus.map
      (l.mapDerivedCategoryPlusFactorsh.hom.app (r.mapHomotopyCategoryPlus.obj P) ≫
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app P))

/-- The pro-etale description `Q(L(d) epsilon_proet^0)` of the common transpose.
Source: Stacks Tag 0FND (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateProEtaleCounitExpression (adj : L ⊣ R) (δ : r ⋙ W ⟶ V ⋙ R)
    (P : HomotopyCategory.Plus D) :
    L.mapDerivedCategoryPlus.obj (W.mapDerivedCategoryPlus.obj
        (DerivedCategory.Plus.Qh.obj (r.mapHomotopyCategoryPlus.obj P))) ⟶
      V.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj P) :=
  L.mapDerivedCategoryPlus.map
      (W.mapDerivedCategoryPlusFactorsh.hom.app (r.mapHomotopyCategoryPlus.obj P) ≫
        DerivedCategory.Plus.Qh.map ((graphMateHomotopyComparison r R V W δ).app P)) ≫
    L.mapDerivedCategoryPlusFactorsh.hom.app
      (R.mapHomotopyCategoryPlus.obj (V.mapHomotopyCategoryPlus.obj P)) ≫
    DerivedCategory.Plus.Qh.map
      (adj.mapHomotopyCategoryPlus.counit.app (V.mapHomotopyCategoryPlus.obj P)) ≫
    V.mapDerivedCategoryPlusFactorsh.inv.app P

/-- The representative compatibility, including both specified adjoint transposes.
Source: Stacks Tag 0FND (blueprint: lem-sp-graph-derived-mate-factorization). -/
def GraphMateRepresentativeCompatibility (adj : l ⊣ r) (adj' : L ⊣ R)
    (adjD : L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus)
    (α : l.mapDerivedCategoryPlus ⋙ V.mapDerivedCategoryPlus ≅
      W.mapDerivedCategoryPlus ⋙ L.mapDerivedCategoryPlus)
    (δ : r ⋙ W ⟶ V ⋙ R)
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) : Prop :=
  graphMateLeft r R V W β = graphMateRight r R V W δ ∧
    ∀ P : HomotopyCategory.Plus D,
      (adjD.homEquiv _ _).symm ((graphMateLeft r R V W β).app P) =
        graphMateEtaleCounitExpression l r L V W adj α P ∧
      (adjD.homEquiv _ _).symm ((graphMateRight r R V W δ).app P) =
        graphMateProEtaleCounitExpression r L R V W adj' δ P ∧
      graphMateEtaleCounitExpression l r L V W adj α P =
        graphMateProEtaleCounitExpression r L R V W adj' δ P

omit [EnoughInjectives D] in
private theorem graphMate_right_transpose (adj' : L ⊣ R)
    (δ : r ⋙ W ⟶ V ⋙ R) (P : HomotopyCategory.Plus D) :
    (adj'.derivedPlus.homEquiv _ _).symm ((graphMateRight r R V W δ).app P) =
      graphMateProEtaleCounitExpression r L R V W adj' δ P := by
  simp only [Adjunction.homEquiv_counit, graphMateRight,
    graphMateProEtaleCounitExpression, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hn := adj'.derivedPlus.counit.naturality (V.mapDerivedCategoryPlusFactorsh.inv.app P)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  erw [hn, adj'.derivedPlus_counit_app_fac_assoc]

private theorem graphMate_left_transpose (adj : l ⊣ r) (adj' : L ⊣ R)
    (α : l.mapDerivedCategoryPlus ⋙ V.mapDerivedCategoryPlus ≅
      W.mapDerivedCategoryPlus ⋙ L.mapDerivedCategoryPlus)
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (hβ : ∀ X, L.mapDerivedCategoryPlus.map (β.app X) ≫
        adj'.derivedPlus.counit.app (V.mapDerivedCategoryPlus.obj X) =
      α.inv.app (r.rightDerivedFunctorPlus.obj X) ≫
        V.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app X))
    (P : HomotopyCategory.Plus D) :
    (adj'.derivedPlus.homEquiv _ _).symm ((graphMateLeft r R V W β).app P) =
      graphMateEtaleCounitExpression l r L V W adj α P := by
  simp only [Adjunction.homEquiv_counit, graphMateLeft,
    graphMateEtaleCounitExpression, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [hβ]
  have hn := α.inv.naturality (r.rightDerivedFunctorPlusUnit.app P)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← V.mapDerivedCategoryPlus.map_comp,
    adj.derivedPlus_counit_app_fac]
  simp only [Functor.map_comp]

private theorem graphMate_baseChange (δ : r ⋙ W ⟶ V ⋙ R) :
    graphMateLeft r R V W (Functor.rightDerivedFunctorPlusBaseChange δ) =
      graphMateRight r R V W δ := by
  apply NatTrans.ext
  funext P
  simpa only [graphMateLeft, graphMateRight, graphMateHomotopyComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.id_comp,
    Category.comp_id] using Functor.rightDerivedFunctorPlusBaseChange_fac_app δ P

private theorem graphMate_compatible (adj : l ⊣ r) (adj' : L ⊣ R)
    (α : l.mapDerivedCategoryPlus ⋙ V.mapDerivedCategoryPlus ≅
      W.mapDerivedCategoryPlus ⋙ L.mapDerivedCategoryPlus)
    (δ : r ⋙ W ⟶ V ⋙ R)
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (hb : β = Functor.rightDerivedFunctorPlusBaseChange δ)
    (hc : ∀ X, α.hom.app (r.rightDerivedFunctorPlus.obj X) ≫
      L.mapDerivedCategoryPlus.map (β.app X) ≫
        adj'.derivedPlus.counit.app (V.mapDerivedCategoryPlus.obj X) =
      V.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app X)) :
    GraphMateRepresentativeCompatibility l r L R V W adj adj' adj'.derivedPlus α δ β := by
  have h : graphMateLeft r R V W β = graphMateRight r R V W δ := by
    rw [hb]
    exact graphMate_baseChange r R V W δ
  refine ⟨h, fun P ↦ ?_⟩
  have hc' (X : DerivedCategory.Plus D) :
      L.mapDerivedCategoryPlus.map (β.app X) ≫
        adj'.derivedPlus.counit.app (V.mapDerivedCategoryPlus.obj X) =
      α.inv.app (r.rightDerivedFunctorPlus.obj X) ≫
        V.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app X) := by
    apply (cancel_epi (α.hom.app _)).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hc X
  have hl := graphMate_left_transpose l r L R V W adj adj' α β hc' P
  have hr := graphMate_right_transpose r L R V W adj' δ P
  exact ⟨hl, hr, hl.symm.trans ((congrArg
    ((adj'.derivedPlus.homEquiv _ _).symm) (congr_app h P)).trans hr)⟩

end Categorical

section Descent
variable {C : Type a} [Category.{av} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type c} [Category.{cv} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [EnoughInjectives D] (S : C ⥤ E) (J : C ⥤ D) (R : D ⥤ E)
  [S.Additive] [J.Additive] [R.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

/-- `Theta = gamma QG` on representatives, with exact source and open-extension factors.
Source: Stacks Tags 0FND and 015F (blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateRepresentativeGraph (G : S ⟶ J ⋙ R) :
    DerivedCategory.Plus.Qh ⋙ S.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ J.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
  S.mapDerivedCategoryPlusFactorsh.hom ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus G ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (J ⋙ R))).inv)
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft J.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight J.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus

/-- Canonical descent of `gamma QG` by fully faithful precomposition with localization.
Source: Stacks Tags 04VG, 0FND and 09AF
(blueprint: lem-sp-graph-derived-mate-factorization). -/
def graphMateDerivedGraph (G : S ⟶ J ⋙ R) :
    S.mapDerivedCategoryPlus ⟶ J.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (DerivedCategory.Plus E)).preimage
      (graphMateRepresentativeGraph S J R G)

private theorem graphMateDerivedGraph_fac (G : S ⟶ J ⋙ R)
    (P : HomotopyCategory.Plus C) :
    (graphMateDerivedGraph S J R G).app (DerivedCategory.Plus.Qh.obj P) =
      S.mapDerivedCategoryPlusFactorsh.hom.app P ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus G).app P) ≫
        R.rightDerivedFunctorPlusUnit.app (J.mapHomotopyCategoryPlus.obj P) ≫
        R.rightDerivedFunctorPlus.map (J.mapDerivedCategoryPlusFactorsh.inv.app P) := by
  have h := congr_app
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C) (DerivedCategory.Plus E)).map_preimage
        (graphMateRepresentativeGraph S J R G)) P
  simpa only [graphMateDerivedGraph, graphMateRepresentativeGraph,
    Functor.whiskeringLeft_obj_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    Category.comp_id] using h

end Descent

section Graph
variable {B : Type a} [Category.{av} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type b} [Category.{bv} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type c} [Category.{cv} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {B' : Type a} [Category.{av} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {C' : Type b} [Category.{bv} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  {D' : Type c} [Category.{cv} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  [EnoughInjectives D] [EnoughInjectives D']
  (S : B ⥤ C) (J : B ⥤ D) (r : D ⥤ C)
  (S' : B' ⥤ C') (J' : B' ⥤ D') (R : D' ⥤ C')
  (V₀ : B ⥤ B') (V : D ⥤ D') (W : C ⥤ C')
  [S.Additive] [J.Additive] [r.Additive] [S'.Additive] [J'.Additive] [R.Additive]
  [V₀.Additive] [V.Additive] [W.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits V₀] [PreservesFiniteColimits V₀]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]

/-- The full compactified graph chain, including its middle representative expression
and its equality after descent to D+. The parameters are instantiated with the specified
geometric maps, not arbitrary witnesses, by the final theorem.
Source: Stacks Tags 0FND and 09AF (blueprint: lem-sp-graph-derived-mate-factorization). -/
def GraphMateGraphCompatibility
    (G : S ⟶ J ⋙ r) (G' : S' ⟶ J' ⋙ R)
    (σ : S ⋙ W ≅ V₀ ⋙ S') (o : J ⋙ V ≅ V₀ ⋙ J')
    (δ : r ⋙ W ⟶ V ⋙ R)
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) : Prop :=
  ∀ (σD : S.mapDerivedCategoryPlus ⋙ W.mapDerivedCategoryPlus ≅
        V₀.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus)
    (oD : J.mapDerivedCategoryPlus ⋙ V.mapDerivedCategoryPlus ≅
        V₀.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus),
    σD = (Functor.mapDerivedCategoryPlusCompIso S W).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫
      Functor.mapDerivedCategoryPlusCompIso V₀ S' →
    oD = (Functor.mapDerivedCategoryPlusCompIso J V).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso o ≪≫
      Functor.mapDerivedCategoryPlusCompIso V₀ J' →
    ∀ (left right : S.mapDerivedCategoryPlus ⋙ W.mapDerivedCategoryPlus ⟶
        V₀.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus),
      left = σD.hom ≫ Functor.whiskerLeft V₀.mapDerivedCategoryPlus
        (graphMateDerivedGraph S' J' R G') →
      right = Functor.whiskerRight (graphMateDerivedGraph S J r G) W.mapDerivedCategoryPlus ≫
        Functor.whiskerLeft J.mapDerivedCategoryPlus β ≫
        Functor.whiskerRight oD.hom R.rightDerivedFunctorPlus →
      ∀ middle : DerivedCategory.Plus.Qh ⋙ S.mapDerivedCategoryPlus ⋙
          W.mapDerivedCategoryPlus ⟶
        DerivedCategory.Plus.Qh ⋙ V₀.mapDerivedCategoryPlus ⋙
          J'.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus,
        middle = Functor.whiskerRight S.mapDerivedCategoryPlusFactorsh.hom
            W.mapDerivedCategoryPlus ≫
          Functor.whiskerRight (Functor.whiskerRight
            (NatTrans.mapHomotopyCategoryPlus G ≫
              (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (J ⋙ r))).inv)
            DerivedCategory.Plus.Qh) W.mapDerivedCategoryPlus ≫
          Functor.whiskerLeft J.mapHomotopyCategoryPlus (graphMateRight r R V W δ) ≫
          Functor.whiskerRight J.mapDerivedCategoryPlusFactorsh.inv
            (V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh
            (Functor.whiskerRight oD.hom R.rightDerivedFunctorPlus) →
        Functor.whiskerLeft DerivedCategory.Plus.Qh left = middle ∧
        middle = Functor.whiskerLeft DerivedCategory.Plus.Qh right ∧ left = right

private theorem graphMate_graph (G : S ⟶ J ⋙ r) (G' : S' ⟶ J' ⋙ R)
    (σ : S ⋙ W ≅ V₀ ⋙ S') (o : J ⋙ V ≅ V₀ ⋙ J')
    (δ : r ⋙ W ⟶ V ⋙ R)
    (β : r.rightDerivedFunctorPlus ⋙ W.mapDerivedCategoryPlus ⟶
      V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (hG : σ.hom ≫ Functor.whiskerLeft V₀ G' =
      Functor.whiskerRight G W ≫ Functor.whiskerLeft J δ ≫ Functor.whiskerRight o.hom R)
    (hβ : graphMateLeft r R V W β = graphMateRight r R V W δ) :
    GraphMateGraphCompatibility S J r S' J' R V₀ V W G G' σ o δ β := by
  intro σD oD hσ ho left right hl hr middle hm
  subst left right middle
  have hs (K : HomotopyCategory.Plus B) := graphMate_iso_factors S W V₀ S' σ K
  have ho' (K : HomotopyCategory.Plus B) := graphMate_iso_factors J V V₀ J' o K
  rw [← hσ] at hs
  rw [← ho] at ho'
  have hK (K : HomotopyCategory.Plus B) :
      (NatTrans.mapHomotopyCategoryPlus σ.hom).app K ≫
        (NatTrans.mapHomotopyCategoryPlus G').app (V₀.mapHomotopyCategoryPlus.obj K) =
      W.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus G).app K) ≫
        (graphMateHomotopyComparison r R V W δ).app (J.mapHomotopyCategoryPlus.obj K) ≫
        R.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus o.hom).app K) := by
    have h := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hG) K
    simpa only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
      graphMate_whiskerLeft, graphMate_whiskerRight, graphMateHomotopyComparison,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.id_comp,
      Category.comp_id] using h
  have hfirst : Functor.whiskerLeft DerivedCategory.Plus.Qh
      (σD.hom ≫ Functor.whiskerLeft V₀.mapDerivedCategoryPlus
        (graphMateDerivedGraph S' J' R G')) =
      Functor.whiskerRight S.mapDerivedCategoryPlusFactorsh.hom W.mapDerivedCategoryPlus ≫
        Functor.whiskerRight (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus G ≫
            (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (J ⋙ r))).inv)
          DerivedCategory.Plus.Qh) W.mapDerivedCategoryPlus ≫
        Functor.whiskerLeft J.mapHomotopyCategoryPlus (graphMateRight r R V W δ) ≫
        Functor.whiskerRight J.mapDerivedCategoryPlusFactorsh.inv
          (V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (Functor.whiskerRight oD.hom R.rightDerivedFunctorPlus) := by
    apply NatTrans.ext
    funext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, graphMateRight,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.comp_id]
    have hn := (graphMateDerivedGraph S' J' R G').naturality
      (V₀.mapDerivedCategoryPlusFactorsh.hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    erw [← cancel_mono (R.rightDerivedFunctorPlus.map
      (J'.mapDerivedCategoryPlus.map (V₀.mapDerivedCategoryPlusFactorsh.hom.app K)))]
    simp only [Category.assoc]
    erw [← hn, graphMateDerivedGraph_fac]
    erw [reassoc_of% hs K, ← DerivedCategory.Plus.Qh.map_comp_assoc, hK K]
    simp only [Functor.map_comp, Category.assoc]
    have hγ := R.rightDerivedFunctorPlusUnit.naturality
      ((NatTrans.mapHomotopyCategoryPlus o.hom).app K)
    simp only [Functor.comp_map] at hγ
    erw [reassoc_of% hγ]
    have hW := W.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus G).app K)
    simp only [Functor.comp_map] at hW
    erw [reassoc_of% hW]
    have hoK : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus o.hom).app K) ≫
        J'.mapDerivedCategoryPlusFactorsh.inv.app (V₀.mapHomotopyCategoryPlus.obj K) =
      V.mapDerivedCategoryPlusFactorsh.inv.app (J.mapHomotopyCategoryPlus.obj K) ≫
        V.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        oD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        J'.mapDerivedCategoryPlus.map (V₀.mapDerivedCategoryPlusFactorsh.hom.app K) := by
      apply (cancel_epi (V.mapDerivedCategoryPlus.map
        (J.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
          V.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj K))).1
      apply (cancel_mono (J'.mapDerivedCategoryPlusFactorsh.hom.app
        (V₀.mapHomotopyCategoryPlus.obj K))).1
      simp only [Category.assoc, Iso.inv_hom_id_app,
        Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (ho' K).symm
    simp only [← R.rightDerivedFunctorPlus.map_comp]
    erw [hoK]
    rfl
  have hsecond :
      Functor.whiskerRight S.mapDerivedCategoryPlusFactorsh.hom W.mapDerivedCategoryPlus ≫
        Functor.whiskerRight (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus G ≫
            (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (J ⋙ r))).inv)
          DerivedCategory.Plus.Qh) W.mapDerivedCategoryPlus ≫
        Functor.whiskerLeft J.mapHomotopyCategoryPlus (graphMateRight r R V W δ) ≫
        Functor.whiskerRight J.mapDerivedCategoryPlusFactorsh.inv
          (V.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (Functor.whiskerRight oD.hom R.rightDerivedFunctorPlus) =
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (Functor.whiskerRight (graphMateDerivedGraph S J r G) W.mapDerivedCategoryPlus ≫
          Functor.whiskerLeft J.mapDerivedCategoryPlus β ≫
          Functor.whiskerRight oD.hom R.rightDerivedFunctorPlus) := by
    erw [← hβ]
    apply NatTrans.ext
    funext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, graphMateLeft, graphMateDerivedGraph_fac,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.comp_id,
      Functor.map_comp, Category.assoc]
    have hn := β.naturality (J.mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
  refine ⟨hfirst, hsecond, ?_⟩
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso B) (DerivedCategory.Plus C')).map_injective
      (hfirst.trans hsecond)

end Graph

/-- The geometric compactification specialization of the full graph chain.
The only local instances are the exactness and additivity of the actual sum extension.
Source: Stacks Tag 09AF (blueprint: lem-sp-graph-derived-mate-factorization). -/
def GraphMateGeometricGraphCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) : Prop :=
  let : (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).Additive :=
    Functor.additive_of_iso
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance)
  let : (etaleSumExtension A e).Additive := (etaleSumAdjunction A e).left_adjoint_additive
  let : PreservesFiniteLimits (etaleSumExtension A e) :=
    (etale_proEtale_graph_sheaf_square A e c).1
  let : PreservesFiniteColimits (etaleSumExtension A e) :=
    (etale_proEtale_graph_sheaf_square A e c).2.1
  GraphMateGraphCompatibility
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (Etale.lowerStar (ModuleCat.{u + 1} A) c.g)
    (etaleSumExtension A e) (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z)
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (Etale.etaleCompactificationGraphMap A e c) (compactifiedProEtaleGraphMap A e c)
    (etaleSumComparisonIso A e)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i)
    (graphComparisonDirectImageMate A c.g) (fixedComparisonDirectImageMatePlus A c.g)

private theorem graphMate_underived_comparison (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (p : Z ⟶ T) :
    graphComparisonDirectImageMate A p =
      lowerStarComparisonUpperStarBaseChange p (ModuleCat.{u + 1} A) := by
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z)
    (lowerStarCompComparisonLowerStarIso p (ModuleCat.{u + 1} A)).inv
  have h := congrArg (fun s ↦ ((mateEquiv
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)) s).natTrans) hi
  simp only [Equiv.apply_symm_apply, Equiv.trans_apply, TwoSquare.equivNatTrans,
    Equiv.coe_fn_symm_mk] at h
  simp only [TwoSquare, TwoSquare.mk, TwoSquare.natTrans, graphComparisonDirectImageMate,
    comparisonCoefficientPullbackIso, Iso.symm_inv, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_hom,
    lowerStarComparisonUpperStarBaseChange, etaleComparisonAdjunction,
    Etale.upperStarLowerStarAdjunction, comparisonCoefficientAdjunction, comparisonAdjunction,
    proEtaleComparisonAdjunction, upperStarLowerStarAdjunction,
    Scheme.smallEtaleTopology] at h ⊢
  convert h.symm using 1
  rfl

private theorem graphMate_representative (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (p : Z ⟶ T) [QuasiCompact p] [QuasiSeparated p] :
    GraphMateRepresentativeCompatibility
      (Etale.upperStar (ModuleCat.{u + 1} A) p)
      (Etale.lowerStar (ModuleCat.{u + 1} A) p)
      (upperStar (ModuleCat.{u + 1} A) p) (lowerStar (ModuleCat.{u + 1} A) p)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
      (comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
      (fixedComparisonPullbackPlus A p) (graphComparisonDirectImageMate A p)
      (fixedComparisonDirectImageMatePlus A p) := by
  have heq : derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).derivedPlus :=
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus _
  rw [heq]
  apply graphMate_compatible
  · exact congrArg Functor.rightDerivedFunctorPlusBaseChange
      (graphMate_underived_comparison A p).symm
  · intro X
    have hc := fixedComparisonDirectImageMatePlus_counit A p X
    simpa only [Etale.rightDerivedLowerStarPlus, Etale.derivedUpperStarLowerStarAdjunctionPlus,
      derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus] using hc

/-- Derived mate factorization, with both transposes and the compactified graph chain.
Source: Stacks derived.tex, Tags 0FND and 015F; proetale.tex, Tag 09AF
(blueprint: lem-sp-graph-derived-mate-factorization).

Proof:
1. The iterated mate/conjugate identity identifies the ordinary graph mate with the
canonical underived direct-image comparison. The specified derived mate is therefore
its right-derived base-change transformation. The defining factorization of that
transformation gives graphMateLeft = graphMateRight on all bounded-below representatives.
2. Expand each derived adjoint transpose using the derived counit. For the left side,
use the specified fixed-comparison counit equation and naturality of the inverse
pullback comparison. For the right side, use naturality of the counit at the inverse
exact localization factor. The normalized derived-counit factorization then gives
exactly the two displayed ordinary-counit expressions; the representative equality
identifies them.
3. Apply the specified sheaf graph square termwise. Compute the derived sum and open
comparison isomorphisms using their exact-functor localization factorizations. The
localization preimage defining each derived graph transformation has exactly the
specified representative graph transformation as its whiskering with Qh.
4. Substitute the localized graph square and use naturality of the pro-etale comparison
unit at the actual open comparison to obtain the first graph equality. Substitute the
representative equality, then use naturality of the derived mate at the inverse open
localization factor to obtain the second equality. Faithful precomposition with Qh
detects equality of the descended graph endpoints. Only exact localization
isomorphisms are canceled; neither gamma nor comparison of injectives is inverted. -/
theorem graph_derived_mate_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (∀ {Z T : Scheme.{u}} (p : Z ⟶ T) [QuasiCompact p] [QuasiSeparated p],
      GraphMateRepresentativeCompatibility
        (Etale.upperStar (ModuleCat.{u + 1} A) p)
        (Etale.lowerStar (ModuleCat.{u + 1} A) p)
        (upperStar (ModuleCat.{u + 1} A) p) (lowerStar (ModuleCat.{u + 1} A) p)
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
        (comparisonUpperStar (ModuleCat.{u + 1} A) T)
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
        (fixedComparisonPullbackPlus A p) (graphComparisonDirectImageMate A p)
        (fixedComparisonDirectImageMatePlus A p)) ∧
    ∀ {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
      [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e),
      GraphMateGeometricGraphCompatibility A e c := by
  refine ⟨fun p ↦ graphMate_representative A p, ?_⟩
  intro U T e _ _ _ _ c
  let : (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).Additive :=
    Functor.additive_of_iso
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance)
  let : (etaleSumExtension A e).Additive := (etaleSumAdjunction A e).left_adjoint_additive
  let : PreservesFiniteLimits (etaleSumExtension A e) :=
    (etale_proEtale_graph_sheaf_square A e c).1
  let : PreservesFiniteColimits (etaleSumExtension A e) :=
    (etale_proEtale_graph_sheaf_square A e c).2.1
  apply graphMate_graph
  · apply NatTrans.ext
    funext M
    exact (etale_proEtale_graph_sheaf_square A e c).2.2.2.2.2.2.choose_spec.2 M
  · exact (graphMate_representative A c.g).1

end AlgebraicGeometry.ProEtale
