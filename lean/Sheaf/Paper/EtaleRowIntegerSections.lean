/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleCETotalSections
public import Sheaf.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import Sheaf.CategoryTheory.ExtCoefficientCocycle
import Sheaf.AlgebraicGeometry.ExtPullbackHomComplex
import Sheaf.AlgebraicGeometry.ConstantSheafPullbackTranspose

/-! # Ordinary comparison before removing extension by zero

Source: Stacks Project, Tags 06XR, 01F8 and 08J6.
(blueprint: lem-weil-pbc-row-integer-sections).
-/

@[expose] public section

universe uNatural v w w'
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Abelian
namespace AlgebraicGeometry.Etale
open Scheme

private theorem homologyMap_apply_of_data
    {S T : ShortComplex AddCommGrpCat.{v}} [S.HasHomology] [T.HasHomology]
    (f : S ⟶ T) (hS : S.LeftHomologyData) (hT : T.LeftHomologyData)
    (γ : ShortComplex.LeftHomologyMapData f hS hT) (x : hS.K) :
    (ShortComplex.homologyMap f) (hS.homologyIso.inv (hS.π x)) =
      hT.homologyIso.inv (hT.π (γ.φK x)) := by
  have hm : hS.homologyIso.inv ≫ ShortComplex.homologyMap f =
      γ.φH ≫ hT.homologyIso.inv := by
    rw [γ.homologyMap_eq]
    simp only [Iso.inv_hom_id_assoc]
  have hπ := ConcreteCategory.congr_hom γ.commπ x
  simp only [ConcreteCategory.comp_apply] at hπ
  have hh := ConcreteCategory.congr_hom hm (hS.π x)
  simp only [ConcreteCategory.comp_apply] at hh
  exact hh.trans (congrArg (fun z ↦ hT.homologyIso.inv z) hπ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyMap_mk
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D]
    {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
    (c : HomComplex K L ⟶ HomComplex K' L') (n : ℤ)
    (x : Cocycle K L n) (y : Cocycle K' L' n)
    (h : (c.f n) (x : Cochain K L n) = (y : Cochain K' L' n)) :
    HomologicalComplex.homologyMap c n ((leftHomologyData K L n).homologyIso.inv
      (CohomologyClass.mk x)) =
      (leftHomologyData K' L' n).homologyIso.inv (CohomologyClass.mk y) := by
  let γ := ShortComplex.leftHomologyMapData
    ((HomologicalComplex.shortComplexFunctor _ _ n).map c)
    (leftHomologyData K L n) (leftHomologyData K' L' n)
  have hK : γ.φK x = y := by
    apply Cocycle.ext
    have hh := ConcreteCategory.congr_hom γ.commi x
    change ((show Cocycle K' L' n from γ.φK x) : Cochain K' L' n) =
      (c.f n) (x : Cochain K L n) at hh
    exact hh.trans h
  have hh := homologyMap_apply_of_data
    ((HomologicalComplex.shortComplexFunctor _ _ n).map c)
    (leftHomologyData K L n) (leftHomologyData K' L' n) γ x
  change HomologicalComplex.homologyMap c n
      ((leftHomologyData K L n).homologyIso.inv (CohomologyClass.mk x)) =
    (leftHomologyData K' L' n).homologyIso.inv (CohomologyClass.mk (γ.φK x)) at hh
  simpa only [hK] using hh


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ext_homComplex_naturality
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' B' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution B') (v : L.obj B ⟶ B')
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫
        (singleFunctor D 0).map v ≫ R'.ι')))
    (q : ℕ) (e : Abelian.Ext A B q) :
    HomologicalComplex.homologyMap (SheafPullbackResolution.homPullbackMap L α _ _ φ) (q : ℤ)
      ((leftHomologyData _ R.cochainComplex (q : ℤ)).homologyIso.inv
        (R.extEquivCohomologyClass e)) =
    (leftHomologyData _ R'.cochainComplex (q : ℤ)).homologyIso.inv
      (R'.extEquivCohomologyClass
        (((Abelian.Ext.mk₀ α).comp (e.mapExactFunctor L) (zero_add q)).comp
          (Abelian.Ext.mk₀ v) (add_zero q))) := by
  obtain ⟨x, hx⟩ := CohomologyClass.mk_surjective (R.extEquivCohomologyClass e)
  have he : e = R.extEquivCohomologyClass.symm (.mk x) := by
    rw [hx, Equiv.symm_apply_apply]
  subst e
  obtain ⟨a, ha, rfl⟩ := Cocycle.fromSingleMk_surjective x (q : ℤ)
    (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl
  have ha' : (α ≫ L.map a ≫ φ.f (q : ℤ)) ≫
      R'.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    have hc := φ.comm (q : ℤ) ((q : ℤ) + 1)
    dsimp only [Functor.mapHomologicalComplex_obj_d] at hc
    simp only [Category.assoc, hc, ← L.map_comp_assoc, ha, L.map_zero,
      zero_comp, comp_zero]
  have hr := InjectiveResolution.ext_mapExactFunctor_coefficient_cocycle L α R R' v φ hφ q a ha ha'
  rw [Equiv.apply_symm_apply, hr, Equiv.apply_symm_apply]
  apply homologyMap_mk
  change Cochain.fromSingleMk
    (α ≫ L.map (Cochain.fromSingleEquiv (zero_add (q : ℤ))
      (Cochain.fromSingleMk a (zero_add (q : ℤ)))) ≫ φ.f (q : ℤ)) (zero_add (q : ℤ)) =
    Cochain.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ)) (zero_add (q : ℤ))
  rw [Cochain.fromSingleEquiv_fromSingleMk]



/-- Apply the sections unit and an integer-indexed comparison.
Source: Stacks Project, Tag 015K; evaluation maps in Tags 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-integer-sections). -/
noncomputable def ceIntegerSectionsMap {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J ⟶ J') :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J' :=
  (NatTrans.mapHomologicalComplex (ceSectionsUnit f) (ComplexShape.up ℤ)).app J ≫
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ

/-- Extend a supplied row map, commuting inverse image with extension by zero.
Source: Stacks Project, Tags 015J and 015K.
(blueprint: lem-weil-pbc-row-integer-sections). -/
noncomputable def ceExtendedRowMap {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J ⟶ J') :
    ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (J.extend ComplexShape.embeddingUpNat) ⟶
      J'.extend ComplexShape.embeddingUpNat :=
  (J.mapExtendIso ComplexShape.embeddingUpNat
    (upperStar AddCommGrpCat.{uNatural + 1} f)).hom ≫
    HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat

private lemma sectionsEquiv_naturality (X : Scheme.{uNatural})
    {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}} (f : F ⟶ F')
    (a : SheafPullbackResolution.ZSheaf X ⟶ F) :
    SheafPullbackResolution.sectionsEquiv X F' (a ≫ f) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map f
        (SheafPullbackResolution.sectionsEquiv X F a) := by
  dsimp only [SheafPullbackResolution.sectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed sections map computes the coefficient and pullback map on Ext.
Source: Stacks Project, Tags 06XR, 01F8 (equations 01F9 and 01FA) and 08J6.
(blueprint: lem-weil-pbc-row-integer-sections).

Proof. Represent an Ext class by a cocycle from the constant integer sheaf into R.
Apply the exact inverse-image functor, precompose with the inverse constant-sheaf
comparison, and postcompose with ψ. The augmentation equality makes the two roofs
agree after postcomposition with v, by ext_mapExactFunctor_coefficient_cocycle.
CohomologyClass.mk and Cocycle.fromSingleMk are surjective, so the equality descends
from cocycles to Hom-complex homology. Evaluation at 1 commutes with postcomposition.
The constant-sheaf transpose identifies evaluation after inverse image with the
sections unit; the terminal-sections comparison identifies that unit with ceSectionsUnit.
Thus complexSectionsIso intertwines homPullbackMap with ceIntegerSectionsMap. Apply
homology, then cancel the Ext/resolution and classSections isomorphisms to obtain the
square below. This argument makes no comparison with nonnegative sections homology;
that extension-by-zero transport is a separate step. Degree zero, zero sheaves, zero
comparisons and empty schemes obey the same cocycle calculation. -/
theorem ceIntegerSectionsIso_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (R : InjectiveResolution G) (R' : InjectiveResolution G')
    (v : (upperStar AddCommGrpCat.{uNatural + 1} f).obj G ⟶ G')
    (ψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map R.ι' ≫ ψ =
      (HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.up ℤ) 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map v ≫ R'.ι')
    (p : ℕ) :
    HomologicalComplex.homologyMap (ceIntegerSectionsMap f ψ) (p : ℤ) ≫
        (SheafPullbackResolution.classSectionsIso Y R'.cochainComplex (p : ℤ)).inv ≫
        (R'.extAddEquivCohomologyClass
      (X := SheafPullbackResolution.ZSheaf Y) (n := p)).toAddCommGrpIso.inv =
      (SheafPullbackResolution.classSectionsIso X R.cochainComplex (p : ℤ)).inv ≫
        (R.extAddEquivCohomologyClass
      (X := SheafPullbackResolution.ZSheaf X) (n := p)).toAddCommGrpIso.inv ≫
        AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) := by sorry

end AlgebraicGeometry.Etale
