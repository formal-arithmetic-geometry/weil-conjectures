/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProjectionFormulaCompactified
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation

/-! Normalization data for the scalar/open exchange argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

local notation "CR" => Scheme.proEtaleConstantRing
local notation "PB" => Scheme.proEtaleConstantRingDerivedPullback
local notation "AD" => Scheme.proEtaleRingDerivedOpenAdjunction
local notation "CC" => Scheme.proEtaleConstantRingComparison
local notation "OE" => Scheme.proEtaleRingDerivedOpenExtension


section LocalizationMate
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ D} {G₂ : D ⥤ E}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
private lemma squareQFac (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : CochainComplex A ℤ) :
    F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app X) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj X) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X ≫
          (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app X ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
  have hF := Functor.mapDerivedCategoryCompIso_fac F₁ F₂ X
  have hG := Functor.mapDerivedCategoryCompIso_fac G₁ G₂ X
  have he := Functor.mapDerivedCategoryNatIso_fac e X
  have hG' : (Functor.mapDerivedCategoryCompIso G₁ G₂).hom.app (DerivedCategory.Q.obj X) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app X) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj X) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hF' : F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
      (Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X) ≫
        (F₁ ⋙ F₂).mapDerivedCategoryFactors.inv.app X := by
    rw [← cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app X)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hF, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]
end LocalizationMate

private lemma unitQ {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (adj : f ⊣ g) (K : CochainComplex C ℤ) :
    adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app K) ≫
      g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have hu : adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        g.mapDerivedCategoryFactors.inv.app _ ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.onDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [hu]
  simp only [Functor.comp_obj, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁]
  [HasDerivedCategory C₂] [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)


private lemma localizedMateQ
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : CochainComplex C₁ ℤ) :
    adj₂.onDerivedCategory.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Q.obj X)) =
      u.mapDerivedCategory.map
          (adj₁.onDerivedCategory.unit.app (DerivedCategory.Q.obj X)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactors.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactors.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactors.hom.app
        ((f₁.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactors.hom.app
        ((v.mapHomologicalComplex (.up ℤ)).obj ((f₁.mapHomologicalComplex (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := adj₂.onDerivedCategory.unit.naturality
    (u.mapDerivedCategoryFactors.inv.app X)
  have h₂ := unitQ adj₂
    ((u.mapHomologicalComplex (.up ℤ)).obj X)
  have h₃ := squareQFac β X
  have h₄ := g₂.mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app X ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp at h₁ h₄
  have h₂' : adj₂.onDerivedCategory.unit.app
      (DerivedCategory.Q.obj ((u.mapHomologicalComplex (.up ℤ)).obj X)) =
      DerivedCategory.Q.map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactors.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactors.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactors.inv.app X ≫
      adj₂.onDerivedCategory.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Q.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactors.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactors.hom.app
        ((f₁.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactors.hom.app
        ((v.mapHomologicalComplex (.up ℤ)).obj ((f₁.mapHomologicalComplex (.up ℤ)).obj X)) =
      DerivedCategory.Q.map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj X) ≫ (g₂.mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app X ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := unitQ adj₁ X
  have k₁' : adj₁.onDerivedCategory.unit.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactors.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactors.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactors.inv.naturality
    ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactors.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactors.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := squareQFac τ
    ((f₁.mapHomologicalComplex (.up ℤ)).obj X)
  dsimp at k₂
  have hR : u.mapDerivedCategoryFactors.inv.app X ≫
      u.mapDerivedCategory.map
        (adj₁.onDerivedCategory.unit.app (DerivedCategory.Q.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactors.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactors.hom.app
        ((f₁.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactors.hom.app
        ((v.mapHomologicalComplex (.up ℤ)).obj ((f₁.mapHomologicalComplex (.up ℤ)).obj X)) =
      DerivedCategory.Q.map ((u.mapHomologicalComplex (.up ℤ)).map
        ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactors.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactors.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
  exact hβ (X.X n)

private lemma localizedMate
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    adj₂.onDerivedCategory.unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map (adj₁.onDerivedCategory.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Q (C := C₁))
    (HomologicalComplex.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Q.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      adj₂.onDerivedCategory.unit.app (u.mapDerivedCategory.obj K) =
      adj₂.onDerivedCategory.unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    adj₂.onDerivedCategory.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ adj₁.onDerivedCategory.unit.app K =
      adj₁.onDerivedCategory.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    adj₁.onDerivedCategory.unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (localizedMateQ adj₁ adj₂ τ β hβ _)]


/-- The descended inverse open exchange has the original open-unit transpose.
Source: Stacks Tags 03S6 and 09AE; `FiniteOpenScalars.inverse_unit_transpose`.
(blueprint: lem-fix-open-base-change-derived-unit)
Proof: the ordinary inverse exchange is `singleBetaInv`, whose component is defined
as the inverse of the open-adjunction Hom equivalence applied to the pulled-back
unit followed by `moduleSquareG.inv`. Thus its transpose is this expression, by the
inverse law of that equivalence. Apply the exact functors degreewise to complexes.
The two open adjunctions descend through localization, retaining their units, and
the comparison is `mapDerivedCategorySquareIso moduleSquareG`. Localization of the
ordinary mate equation therefore gives the displayed identity on Q of every complex.
Every derived object is isomorphic to such a Q-object. Naturality of the units and
of the descended comparisons transports the identity to an arbitrary K. -/
theorem openBaseChangeDerivedUnit {A : Type u} [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (K : DerivedCategory (Scheme.proEtaleRingModules U (CR U A))) :
    (AD j' (CR X' A) (CR U' A) (CC j' A)).unit.app ((PB A gU).obj K) ≫
      (PB A j').map
        ((StrictTower.singleBeta (ULift.{u + 1, u} A) gU j' j g sq.toCommSq.w
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
            sq.hom_fst sq.hom_snd)).inv.app K) =
      (PB A gU).map ((AD j (CR X A) (CR U A) (CC j A)).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso
          (StrictTower.moduleSquareG (ULift.{u + 1, u} A) gU j' j g
            sq.toCommSq.w)).inv.app ((OE j (CR X A) (CR U A) (CC j A)).obj K) := by
  let B := ULift.{u + 1, u} A
  let hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let beta : StrictTower.modulePullback B gU ⋙ StrictTower.moduleJ B j' ≅
      StrictTower.moduleJ B j ⋙ StrictTower.modulePullback B g :=
    @asIso _ _ _ _ (StrictTower.singleBetaInv B gU j' j g sq.toCommSq.w)
      (StrictTower.singleBetaInv_isIso B gU j' j g sq.toCommSq.w hsq)
  have hb (M : StrictTower.Modules B U) :
      (StrictTower.moduleJAdj B j').unit.app ((StrictTower.modulePullback B gU).obj M) ≫
        (StrictTower.modulePullback B j').map (beta.hom.app M) =
      (StrictTower.modulePullback B gU).map ((StrictTower.moduleJAdj B j).unit.app M) ≫
        (StrictTower.moduleSquareG B gU j' j g sq.toCommSq.w).inv.app
          ((StrictTower.moduleJ B j).obj M) := by
    exact ((StrictTower.moduleJAdj B j').homEquiv _ _).apply_symm_apply _
  have h := localizedMate (StrictTower.moduleJAdj B j) (StrictTower.moduleJAdj B j')
    (StrictTower.moduleSquareG B gU j' j g sq.toCommSq.w).symm beta hb K
  simp only [StrictTower.singleBeta, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc,
    beta, B, Scheme.proEtaleRingDerivedOpenAdjunction, StrictTower.moduleJAdj,
    Adjunction.onDerivedCategory] at h ⊢
  convert h using 1 <;> rfl

end AlgebraicGeometry.ProEtale
