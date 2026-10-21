/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleTransport
public import Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Total-limit comparison and transposes of augmented tower arrows

Source: Stacks Project, Cohomology on Sites, Tags 0A07, 07A6 and 0940;
Derived Categories, Tags 08BJ, 070I and 09T5. The combined normalization is
an agent auxiliary (blueprint: lem-pur-tower-limit-transpose-normalization).

Positive level `n + 1` is encoded by `n : ℕ`. All categories are ordinary
unbounded module derived categories. The comparison is specified by its
common-underived-composite equation, rather than just its projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048


universe u w a v x y

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantLeftModuleInverseImage

namespace CategoryTheory.TowerLimitTransposeNormalization

-- The representative equation for conjugation follows from its counit equation.
private theorem conjugate_normalization
    {B E B' E' : Type*} [Category B] [Category E] [Category B'] [Category E']
    {F F' : B ⥤ E} {G G' : E ⥤ B}
    {FD FD' : B' ⥤ E'} {GD GD' : E' ⥤ B'}
    (a : F ⊣ G) (b : F' ⊣ G') (ad : FD ⊣ GD) (bd : FD' ⊣ GD')
    (QB : B ⥤ B') (QE : E ⥤ E') (e : F' ≅ F) (ed : FD' ≅ FD)
    (p : QB ⋙ FD ≅ F ⋙ QE) (p' : QB ⋙ FD' ≅ F' ⋙ QE)
    (β : ∀ H, QB.obj (G.obj H) ⟶ GD.obj (QE.obj H))
    (β' : ∀ H, QB.obj (G'.obj H) ⟶ GD'.obj (QE.obj H))
    (hβ : ∀ H, FD.map (β H) ≫ ad.counit.app (QE.obj H) =
      p.hom.app (G.obj H) ≫ QE.map (a.counit.app H))
    (hβ' : ∀ H, FD'.map (β' H) ≫ bd.counit.app (QE.obj H) =
      p'.hom.app (G'.obj H) ≫ QE.map (b.counit.app H))
    (he : ∀ X, ed.hom.app (QB.obj X) ≫ p.hom.app X =
      p'.hom.app X ≫ QE.map (e.hom.app X)) (H : E) :
    β H ≫ (conjugateIsoEquiv ad bd ed).hom.app (QE.obj H) =
      QB.map ((conjugateIsoEquiv a b e).hom.app H) ≫ β' H := by
  apply (bd.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [conjugateIsoEquiv_apply_hom]
  erw [conjugateEquiv_counit ad bd ed.hom (QE.obj H)]
  erw [reassoc_of% ed.hom.naturality (β H)]
  rw [hβ, ← Category.assoc, he, Category.assoc]
  erw [hβ']
  erw [reassoc_of% p'.hom.naturality ((conjugateIsoEquiv a b e).hom.app H)]
  simp only [← Functor.map_comp]
  congr 2
  exact (conjugateEquiv_counit a b e.hom H).symm

private theorem conjugate_homEquiv
    {B E : Type*} [Category B] [Category E]
    {F F' : B ⥤ E} {G G' : E ⥤ B}
    (a : F ⊣ G) (b : F' ⊣ G') (e : F' ≅ F)
    (M : B) (V : E) (f : F.obj M ⟶ V) :
    b.homEquiv M V (e.hom.app M ≫ f) =
      a.homEquiv M V f ≫ (conjugateIsoEquiv a b e).hom.app V := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show G.map f ≫ (conjugateIsoEquiv a b e).hom.app V =
    (conjugateIsoEquiv a b e).hom.app (F.obj M) ≫ G'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem ordinary_limit_comparison
    {B E : Type*} [Category B] [Category E]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
    {F : B ⥤ E} {G : E ⥤ B} (a : F ⊣ G) [PreservesLimitsOfShape ℕᵒᵖ G]
    (H : ℕᵒᵖ ⥤ E) :
    (conjugateIsoEquiv
      (a.comp (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣ lim))
      ((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim).comp (a.whiskerRight ℕᵒᵖ))
      (Functor.compConstIso ℕᵒᵖ F).symm).hom.app H =
      (preservesLimitNatIso G (J := ℕᵒᵖ)).hom.app H := by
  apply limit.hom_ext
  intro n
  simp [conjugateIsoEquiv, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Adjunction.comp_counit_app, constLimAdj]

section Representatives

variable {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
  [Abelian.HasKInjectiveResolutions E]
  {F : B ⥤ E} {G : E ⥤ B} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cochain_unit (a : F ⊣ G) (H : CochainComplex B ℤ) :
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj H) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app H) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app H) ≫
        UnboundedExactTower.cochainUnit G ((F.mapHomologicalComplex (.up ℤ)).obj H) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso B (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient B (.up ℤ)).obj H)
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app _) = _ at h
  simp only [UnboundedExactTower.cochainUnit, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [Functor.map_id] at h
  repeat erw [Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id] at h
  repeat erw [Category.comp_id]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cochain_counit (a : F ⊣ G) (H : CochainComplex E ℤ) :
    F.mapDerivedCategory.map (UnboundedExactTower.cochainUnit G H) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj H) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj H) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app H) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso E (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient E (.up ℤ)).obj H)
  change F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app _) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj H)) ≫ _ at h
  simp only [UnboundedExactTower.cochainUnit, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp, Category.assoc] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [Functor.map_id] at h
  repeat erw [Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  exact h

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory.{w} E']
  [Abelian.HasKInjectiveResolutions E']
  {F' : E ⥤ E'} {G' : E' ⥤ E} [F'.Additive] [G'.Additive]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

private def compositeFactors :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ F'.mapDerivedCategory) ≅
      (F.mapHomologicalComplex (.up ℤ) ⋙ F'.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors F'.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) F'.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm

-- The comparison for a composite right derived functor is normalized by both counits.
private theorem cochain_comp_counit (a : F ⊣ G) (b : F' ⊣ G')
    (H : CochainComplex E' ℤ) :
    (F.mapDerivedCategory ⋙ F'.mapDerivedCategory).map
        (UnboundedExactTower.cochainUnit G ((G'.mapHomologicalComplex (.up ℤ)).obj H) ≫
          G.rightDerivedFunctor.map (UnboundedExactTower.cochainUnit G' H)) ≫
        (a.mapDerivedCategoryRightDerivedAdjunction.comp
          b.mapDerivedCategoryRightDerivedAdjunction).counit.app (DerivedCategory.Q.obj H) =
      F'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj
            ((G'.mapHomologicalComplex (.up ℤ)).obj H))) ≫
        F'.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((G.mapHomologicalComplex (.up ℤ)).obj
              ((G'.mapHomologicalComplex (.up ℤ)).obj H))) ≫
        DerivedCategory.Q.map
          (((a.mapHomologicalComplex (.up ℤ)).comp
            (b.mapHomologicalComplex (.up ℤ))).counit.app H) := by
  have hn := a.mapDerivedCategoryRightDerivedAdjunction.counit.naturality
    (UnboundedExactTower.cochainUnit G' H)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hh : F.mapDerivedCategory.map
        (UnboundedExactTower.cochainUnit G ((G'.mapHomologicalComplex (.up ℤ)).obj H) ≫
          G.rightDerivedFunctor.map (UnboundedExactTower.cochainUnit G' H)) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app
          (G'.rightDerivedFunctor.obj (DerivedCategory.Q.obj H)) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj
          ((G'.mapHomologicalComplex (.up ℤ)).obj H)) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app
          ((G'.mapHomologicalComplex (.up ℤ)).obj H)) ≫
        UnboundedExactTower.cochainUnit G' H := by
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, cochain_counit,
      Category.assoc]
  simp only [Functor.comp_map, Adjunction.comp_counit_app]
  rw [← F'.mapDerivedCategory.map_comp_assoc, hh]
  simp only [Functor.map_comp, Category.assoc]
  erw [cochain_counit b]
  erw [F'.mapDerivedCategoryFactors_hom_naturality_assoc]

end Representatives

section Limits

variable (T : Type a) [Category.{v} T] [Abelian T] [HasLimitsOfShape ℕᵒᵖ T]

/-- The ordinary strict tower limit, with its existing Mathlib construction.
Source: Stacks 0940 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerLimit : (ℕᵒᵖ ⥤ T) ⥤ T := lim

/-- Additivity of the existing limit functor, from preservation of binary products.
Source: Stacks 0940 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance towerLimitAdditive : (towerLimit T).Additive :=
  Functor.additive_of_preserves_binary_products (towerLimit T)

variable [HasDerivedCategory.{w} T] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ T)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ T)]

/-- The actual derived constant/limit adjunction, derived from `constLimAdj`.
Its unit supplies the specified identification with a constant tower's total limit.
Source: Stacks 0940 and 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev limitAdjunction :
    (Functor.const ℕᵒᵖ : T ⥤ (ℕᵒᵖ ⥤ T)).mapDerivedCategory ⊣
      (towerLimit T).rightDerivedFunctor :=
  (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ (ℕᵒᵖ ⥤ T)) ⊣
    towerLimit T).mapDerivedCategoryRightDerivedAdjunction


/-- On representatives the derived constant/limit unit is induced by the ordinary
cone of identity maps. On a diagonal K-injective representative all comparisons
are isomorphisms, so this is precisely the identity normalization.
Source: Stacks 0940, 08BJ, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
def ConstantUnitNormalization : Prop :=
  ∀ H : CochainComplex T ℤ, H.IsKInjective →
    (limitAdjunction T).unit.app (DerivedCategory.Q.obj H) ≫
        (towerLimit T).rightDerivedFunctor.map
          ((Functor.const ℕᵒᵖ : T ⥤ _).mapDerivedCategoryFactors.hom.app H) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ _) ⊣ towerLimit T).unit (.up ℤ)).app H) ≫
        UnboundedExactTower.cochainUnit (towerLimit T)
          (((Functor.const ℕᵒᵖ : T ⥤ _).mapHomologicalComplex (.up ℤ)).obj H)

private def evaluationZeroConstAdjunction :
    (evaluation ℕᵒᵖ T).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun W ↦ {
        app := fun n ↦ W.map (homOfLE (Nat.zero_le n.unop)).op
        naturality := by
          intro n m t
          change W.map t ≫ W.map _ = W.map _ ≫ 𝟙 _
          rw [Category.comp_id, ← W.map_comp]
          congr 1 }
      naturality := by
        intro W V t
        ext n
        exact (t.naturality (homOfLE (Nat.zero_le n.unop)).op).symm }
    counit := { app := fun X ↦ 𝟙 X }
    left_triangle := by ext W; dsimp; simp
    right_triangle := by ext X n; dsimp; simp }

private theorem cochainUnit_isIso
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions B] (G : B ⥤ E) [G.Additive]
    (H : CochainComplex B ℤ) [H.IsKInjective] :
    IsIso (UnboundedExactTower.cochainUnit G H) := by
  unfold UnboundedExactTower.cochainUnit
  infer_instance

private theorem constant_unit_normalization : ConstantUnitNormalization T := by
  intro H _
  exact cochain_unit (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ _) ⊣ towerLimit T) H

variable [Abelian.HasKInjectiveResolutions T]

private theorem limit_unit_isIso : IsIso (limitAdjunction T).unit := by
  let := (evaluationZeroConstAdjunction T).preservesKInjectiveComplexes
  have h : ∀ H : CochainComplex T ℤ, H.IsKInjective →
      IsIso ((limitAdjunction T).unit.app (DerivedCategory.Q.obj H)) := by
    intro H hH
    let := hH
    let := cochainUnit_isIso (towerLimit T)
      (((Functor.const ℕᵒᵖ : T ⥤ _).mapHomologicalComplex (.up ℤ)).obj H)
    let a₀ := (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ _) ⊣ towerLimit T)
    have : IsIso a₀.unit := by
      exact a₀.unit_isIso_of_L_fully_faithful
    have : IsIso ((a₀.mapHomologicalComplex (.up ℤ)).unit.app H) := by
      exact HomologicalComplex.Hom.isIso_of_components _
    have he := cochain_unit a₀ H
    have : IsIso ((limitAdjunction T).unit.app (DerivedCategory.Q.obj H) ≫
        (towerLimit T).rightDerivedFunctor.map
          ((Functor.const ℕᵒᵖ : T ⥤ _).mapDerivedCategoryFactors.hom.app H)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((towerLimit T).rightDerivedFunctor.map
        ((Functor.const ℕᵒᵖ : T ⥤ _).mapDerivedCategoryFactors.hom.app H))
  have : ∀ X, IsIso ((limitAdjunction T).unit.app X) := by
    intro X
    obtain ⟨H, hH, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage X)
    let := hq
    let := h H hH
    let e : X ≅ DerivedCategory.Q.obj H :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map q)
    have hi : IsIso (e.hom ≫ (limitAdjunction T).unit.app (DerivedCategory.Q.obj H)) :=
      inferInstance
    have hn := (limitAdjunction T).unit.naturality e.hom
    simp only [Functor.id_map] at hn
    rw [hn] at hi
    exact (isIso_comp_right_iff _ _).mp hi
  exact NatIso.isIso_of_isIso_app _

end Limits

private abbrev termwise {B E : Type*} [Category B] [Category E] (F : B ⥤ E) :
    (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ E) :=
  (Functor.whiskeringRight ℕᵒᵖ B E).obj F

section GenericNormalization

variable {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
  [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ E)]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions E]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
  {F : B ⥤ E} {G : E ⥤ B} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape ℕᵒᵖ G]
  (adj : F ⊣ G)

private def comparison :
    (towerLimit E).rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅
      (termwise G).rightDerivedFunctor ⋙ (towerLimit B).rightDerivedFunctor :=
  conjugateIsoEquiv ((adj.mapDerivedCategoryRightDerivedAdjunction).comp (limitAdjunction E))
    ((limitAdjunction B).comp ((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction))
    (UnboundedExactTower.constantInterchange F)

private def cochainInterchange (F : B ⥤ E) [F.Additive] :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ) ⋙
        (termwise F).mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        (Functor.const ℕᵒᵖ : E ⥤ _).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F).symm (.up ℤ)

omit [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions E]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)] in
private theorem interchange_fac (F : B ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (H : CochainComplex B ℤ) :
    (UnboundedExactTower.constantInterchange F).hom.app
        (DerivedCategory.Q.obj H) ≫
        (compositeFactors (F := F)
          (F' := Functor.const ℕᵒᵖ)).hom.app H =
      (compositeFactors (F := Functor.const ℕᵒᵖ) (F' := termwise F)).hom.app H ≫
        DerivedCategory.Q.map ((cochainInterchange F).hom.app H) := by
  simp only [UnboundedExactTower.constantInterchange, compositeFactors, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fac F
    (Functor.const ℕᵒᵖ) H
  have hc' := Functor.mapDerivedCategoryCompIso_fac
    (Functor.const ℕᵒᵖ) (termwise F) H
  erw [show (Functor.mapHomologicalComplexCompIso
    (Iso.refl (F ⋙ Functor.const ℕᵒᵖ)) (.up ℤ)).hom.app H = 𝟙 _ from rfl,
    Functor.map_id, Category.comp_id] at hc
  erw [show (Functor.mapHomologicalComplexCompIso
    (Iso.refl ((Functor.const ℕᵒᵖ : B ⥤ _) ⋙ termwise F))
      (.up ℤ)).hom.app H = 𝟙 _ from rfl, Functor.map_id, Category.comp_id] at hc'
  erw [hc, Functor.mapDerivedCategoryNatIso_fac]
  erw [← hc']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

omit [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ E)]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions E]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem cochain_comparison (H : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) :
    (conjugateIsoEquiv
      ((adj.mapHomologicalComplex (.up ℤ)).comp
        ((constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣
          towerLimit E).mapHomologicalComplex (.up ℤ)))
      (((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣
          towerLimit B).mapHomologicalComplex (.up ℤ)).comp
        ((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)))
      (cochainInterchange F)).hom.app H =
    (NatTrans.mapHomologicalComplex
      (preservesLimitNatIso G (J := ℕᵒᵖ)).hom (.up ℤ)).app H := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (conjugateIsoEquiv
    (adj.comp (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣ lim))
    ((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim).comp (adj.whiskerRight ℕᵒᵖ))
    (Functor.compConstIso ℕᵒᵖ F).symm).hom.app (H.X k) = _
  exact ordinary_limit_comparison adj (H.X k)

omit [Abelian.HasKInjectiveResolutions B] in
private theorem comparison_fac (H : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) :
    UnboundedExactTower.cochainUnit G
        (((towerLimit E).mapHomologicalComplex (.up ℤ)).obj H) ≫
      G.rightDerivedFunctor.map
        (UnboundedExactTower.cochainUnit (towerLimit E) H) ≫
      (comparison adj).hom.app (DerivedCategory.Q.obj H) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (preservesLimitNatIso G (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
      UnboundedExactTower.cochainUnit (towerLimit B)
        (((termwise G).mapHomologicalComplex (.up ℤ)).obj H) ≫
      (towerLimit B).rightDerivedFunctor.map
        (UnboundedExactTower.cochainUnit (termwise G) H) := by
  have h := conjugate_normalization
    ((adj.mapHomologicalComplex (.up ℤ)).comp
      ((constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣
        towerLimit E).mapHomologicalComplex (.up ℤ)))
    (((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣
        towerLimit B).mapHomologicalComplex (.up ℤ)).comp
      ((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)))
    ((adj.mapDerivedCategoryRightDerivedAdjunction).comp (limitAdjunction E))
    ((limitAdjunction B).comp ((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction))
    DerivedCategory.Q DerivedCategory.Q (cochainInterchange F)
    (UnboundedExactTower.constantInterchange F)
    (compositeFactors (F := F) (F' := Functor.const ℕᵒᵖ))
    (compositeFactors (F := Functor.const ℕᵒᵖ) (F' := termwise F))
    (fun H ↦ UnboundedExactTower.cochainUnit G
        (((towerLimit E).mapHomologicalComplex (.up ℤ)).obj H) ≫
      G.rightDerivedFunctor.map
        (UnboundedExactTower.cochainUnit (towerLimit E) H))
    (fun H ↦ UnboundedExactTower.cochainUnit (towerLimit B)
        (((termwise G).mapHomologicalComplex (.up ℤ)).obj H) ≫
      (towerLimit B).rightDerivedFunctor.map
        (UnboundedExactTower.cochainUnit (termwise G) H))
    (fun H ↦ by
      simpa [compositeFactors] using cochain_comp_counit adj
        (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣ towerLimit E) H)
    (fun H ↦ by
      simpa [compositeFactors] using cochain_comp_counit
        (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ towerLimit B)
        (adj.whiskerRight ℕᵒᵖ) H)
    (interchange_fac F) H
  erw [cochain_comparison adj H] at h
  simpa only [comparison, Category.assoc] using h

private theorem normalization :
    ∃ e : (towerLimit E).rightDerivedFunctor ⋙
        G.rightDerivedFunctor ≅
      (termwise G).rightDerivedFunctor ⋙ (towerLimit B).rightDerivedFunctor,
      (∀ H : CochainComplex (ℕᵒᵖ ⥤ E) ℤ,
        UnboundedExactTower.cochainUnit G
            (((towerLimit E).mapHomologicalComplex (.up ℤ)).obj H) ≫
          G.rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerLimit E) H) ≫
          e.hom.app (DerivedCategory.Q.obj H) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (preservesLimitNatIso G (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
          UnboundedExactTower.cochainUnit (towerLimit B)
            (((termwise G).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (towerLimit B).rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (termwise G) H)) ∧
      IsIso (limitAdjunction B).unit ∧
      IsIso (limitAdjunction E).unit ∧
      ConstantUnitNormalization B ∧
      ConstantUnitNormalization E ∧
      (∀ (M : DerivedCategory.{w} B)
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ E))
          (c : M ⟶ (towerLimit B).rightDerivedFunctor.obj
            ((termwise G).rightDerivedFunctor.obj V)),
        (limitAdjunction E).homEquiv
            (F.mapDerivedCategory.obj M) V
            ((UnboundedExactTower.constantInterchange F).inv.app M ≫
              (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv
                ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj M) V).symm
                (((limitAdjunction B).homEquiv M
                  ((termwise G).rightDerivedFunctor.obj V)).symm c)) =
          ((adj.mapDerivedCategoryRightDerivedAdjunction).homEquiv M
            ((towerLimit E).rightDerivedFunctor.obj V)).symm (c ≫ e.inv.app V)) ∧
      (∀ (M : DerivedCategory.{w} B)
          (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ E))
          (b : (termwise F).mapDerivedCategory.obj Z ⟶ V)
          (j : (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj M ⟶ Z),
        (adj.mapDerivedCategoryRightDerivedAdjunction).homEquiv M
            ((towerLimit E).rightDerivedFunctor.obj V)
            ((limitAdjunction E).homEquiv
              (F.mapDerivedCategory.obj M) V
              ((UnboundedExactTower.constantInterchange F).inv.app M ≫
                (termwise F).mapDerivedCategory.map j ≫ b)) =
          (limitAdjunction B).unit.app M ≫
            (towerLimit B).rightDerivedFunctor.map j ≫
            (towerLimit B).rightDerivedFunctor.map
              (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv Z V b) ≫
            e.inv.app V) := by
  -- Construct the specified comparison as adj mate, then use its Hom compatibility.
  refine ⟨comparison adj, comparison_fac adj, limit_unit_isIso _, limit_unit_isIso _,
    constant_unit_normalization _, constant_unit_normalization _, ?_, ?_⟩
  · intro M V c
    apply ((adj.mapDerivedCategoryRightDerivedAdjunction).homEquiv M _).injective
    have h := conjugate_homEquiv
      ((adj.mapDerivedCategoryRightDerivedAdjunction).comp (limitAdjunction E))
      ((limitAdjunction B).comp ((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction))
      (UnboundedExactTower.constantInterchange F) M V
      ((UnboundedExactTower.constantInterchange F).inv.app M ≫
        (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv _ V).symm
          (((limitAdjunction B).homEquiv M _).symm c))
    simp only [Adjunction.comp_homEquiv] at h
    change (limitAdjunction B).homEquiv M _
      (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv _ V
        ((UnboundedExactTower.constantInterchange F).hom.app M ≫
          (UnboundedExactTower.constantInterchange F).inv.app M ≫
          (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv
            _ V).symm (((limitAdjunction B).homEquiv M _).symm c))) =
      adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M _
        ((limitAdjunction E).homEquiv _ V
          ((UnboundedExactTower.constantInterchange F).inv.app M ≫
            (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv
              _ V).symm (((limitAdjunction B).homEquiv M _).symm c))) ≫
        (comparison adj).hom.app V at h
    erw [Iso.hom_inv_id_app_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    apply (cancel_mono ((comparison adj).hom.app V)).1
    apply Eq.trans h.symm
    symm
    erw [Equiv.apply_symm_apply]
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id c
  · intro M Z V b j
    have h := conjugate_homEquiv
      ((adj.mapDerivedCategoryRightDerivedAdjunction).comp (limitAdjunction E))
      ((limitAdjunction B).comp ((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction))
      (UnboundedExactTower.constantInterchange F) M V
      ((UnboundedExactTower.constantInterchange F).inv.app M ≫
        (termwise F).mapDerivedCategory.map j ≫ b)
    simp only [Adjunction.comp_homEquiv] at h
    change (limitAdjunction B).homEquiv M _
      (((adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction).homEquiv _ V
        ((UnboundedExactTower.constantInterchange F).hom.app M ≫
          (UnboundedExactTower.constantInterchange F).inv.app M ≫
          (termwise F).mapDerivedCategory.map j ≫ b)) =
      adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M _
        ((limitAdjunction E).homEquiv _ V
          ((UnboundedExactTower.constantInterchange F).inv.app M ≫
            (termwise F).mapDerivedCategory.map j ≫ b)) ≫
        (comparison adj).hom.app V at h
    erw [Iso.hom_inv_id_app_assoc] at h
    apply (cancel_mono ((comparison adj).hom.app V)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    dsimp only [comparison]
    repeat erw [Category.comp_id]
    erw [← h]
    erw [Adjunction.homEquiv_naturality_left]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]


end GenericNormalization

section Coefficients

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type u} [CommRing A]
  [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {U : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
  {adj : L ⊣ U} {hL : PreservesFiniteLimits L}
  (d : ConstantLeftModuleInverseImageLift J K A L U adj hL)

/-- Reuse the supplied constant-module inverse image's additive structure.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseAdditive : d.moduleFunctor.Additive := d.additive

/-- Reuse exactness of the canonical constant-module inverse image.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseFiniteLimits : PreservesFiniteLimits d.moduleFunctor := d.preservesFiniteLimits

/-- Reuse exactness of the canonical constant-module inverse image.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseFiniteColimits : PreservesFiniteColimits d.moduleFunctor :=
  d.preservesFiniteColimits

/-- The supplied module direct image preserves limits by its actual module adjunction.
Source: Stacks 03D7 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance directLimits : PreservesLimitsOfSize.{x, y} d.moduleDirect :=
  d.moduleAdj.rightAdjoint_preservesLimits

/-- Additivity of module direct image, using its preservation of binary products.
Source: Stacks 03D7 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance directAdditive : d.moduleDirect.Additive :=
  Functor.additive_of_preserves_binary_products d.moduleDirect

variable [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A)]

/-- Termwise direct image on strict towers, before deriving.
Source: Stacks 0A07 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerDirect : (ℕᵒᵖ ⥤ Modules K A) ⥤ (ℕᵒᵖ ⥤ Modules J A) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules K A) (Modules J A)).obj d.moduleDirect

/-- Exact termwise inverse image on strict towers, before localization.
Source: Stacks 00YV and 015F
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerInverse : (ℕᵒᵖ ⥤ Modules J A) ⥤ (ℕᵒᵖ ⥤ Modules K A) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules J A) (Modules K A)).obj d.moduleFunctor

/-- The canonical ordinary module derived adjunction, with its actual counit.
Source: Stacks 07A6, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev moduleAdjunction : d.moduleFunctor.mapDerivedCategory ⊣
    d.moduleDirect.rightDerivedFunctor := d.moduleAdj.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical tower derived adjunction, derived from the termwise module adjunction.
Source: Stacks 07A6, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerAdjunction : (towerInverse d).mapDerivedCategory ⊣
    (towerDirect d).rightDerivedFunctor :=
  (d.moduleAdj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction

/-- The fixed direct-image/total-limit comparison identifies the composite Hom bijection
and every augmented-arrow transpose, including the actual derived counits.

Source: Stacks Project, Cohomology on Sites, 0A07 (first proof), 07A6 and 0940;
Derived Categories, 08BJ, 070I and 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization).

`d` is any presentation of the canonical constant-coefficient module lift of the
geometric adjunction, not an arbitrary pair of module functors. `J` is the target
site and `K` the source site. The ideal `_I` is unrestricted; its quotients do not
enter this constant-A assertion. The first equation uniquely normalizes `a` as the
comparison of the common underived composite in
lem-weil-ringed-tower-pushforward-limit-comparison. The next two clauses say that
the actual units of the derived constant/limit adjunctions are isomorphisms. Their
inverses are the diagonal K-injective normalization `Rlim Δ ≅ 1`; thus a unit still
visible in the final formula is precisely the suppressed source identification.
The Hom equalities are universally quantified, so include zero objects, identity
morphisms, constant towers and the counit specialization. All operations in these
equalities are natural Hom equivalences or natural transformations.

Proof (the seven steps of the node):
1. Use lem-pe-constant-left-module-inverse-image and
   lem-weil-pbc-ringed-topoi-module-adjunction for the exact module adjunction.
   By lem-weil-tower-category-levelwise-abelian it extends termwise to towers;
   lem-weil-pbc-exact-functor-derived-factorization descends its exact left functors
   and the constant/inverse-image identity.
2. The ordinary constant/limit Hom bijection is `constLimAdj`. Since level 1 is
   terminal in the tower index, evaluation there is left adjoint to constants.
   It is exact, so lem-weil-pbc-right-adjoint-preserves-kinjective makes constants
   preserve K-injectives. The same criterion makes limit preserve K-injectives.
   Compute Rlim of a diagonal K-injective as that same complex, with identity unit,
   by lem-weil-pbc-ringed-strict-tower-homotopy-limit.
3. Use lem-weil-pbc-diagram-site-realization and prop-pur-kinjective-resolutions-exist
   for a K-injective tower H representing V. Direct image, tower direct image and
   limit preserve K-injectives, hence lem-weil-pbc-kinjective-total-derived computes
   both composites on H. The fixed comparison from
   lem-weil-ringed-tower-pushforward-limit-comparison is the ordinary limit.post
   comparison on H, giving exactly the first equation below.
4. By lem-weil-pbc-kinjective-hom-derived the displayed Hom sets are homotopy Hom
   sets into these representatives. By lem-weil-pbc-termwise-adjunction-homotopy
   their adjunction bijections are the ordinary termwise ones. The counit equation
   in lem-sc-derived-adjunction-from-underived identifies these with the actual
   canonical derived adjunctions, and identifies the constant/limit unit as in step 2.
5. For a chain map c:B -> lim U^J H, the first two transposes have component
   eps_(H_n) F(pi_n c). The last transpose is the unique chain map with these
   components. Naturality of the ordinary counit and pi_n a = U(pi_n) show that
   transposing c followed by a inverse has these very components. Equality is
   checked in complexes, then localized; no detection by derived projections is used.
6. Put k = j followed by the tower adjunct of b. Its tower transpose is G(j) followed
   by b. Apply step 5 and both constant/limit adjunctions; their units give exactly
   the last formula below and their inverses give the source identifications.
7. Naturality of each Hom bijection and of the fixed comparison proves naturality
   in M,V,Z,b,j. Only exact constant pullback and K-injective resolutions were used:
   neither perfectness, completeness, boundedness nor exact products is needed. -/
theorem tower_limit_transpose_normalization
    [IsNoetherianRing A] (_I : Ideal A) :
    ∃ a : (towerLimit (Modules K A)).rightDerivedFunctor ⋙
        d.moduleDirect.rightDerivedFunctor ≅
      (towerDirect d).rightDerivedFunctor ⋙ (towerLimit (Modules J A)).rightDerivedFunctor,
      (∀ H : CochainComplex (ℕᵒᵖ ⥤ Modules K A) ℤ,
        UnboundedExactTower.cochainUnit d.moduleDirect
            (((towerLimit (Modules K A)).mapHomologicalComplex (.up ℤ)).obj H) ≫
          d.moduleDirect.rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerLimit (Modules K A)) H) ≫
          a.hom.app (DerivedCategory.Q.obj H) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (preservesLimitNatIso d.moduleDirect (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
          UnboundedExactTower.cochainUnit (towerLimit (Modules J A))
            (((towerDirect d).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (towerLimit (Modules J A)).rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerDirect d) H)) ∧
      IsIso (limitAdjunction (Modules J A)).unit ∧
      IsIso (limitAdjunction (Modules K A)).unit ∧
      ConstantUnitNormalization (Modules J A) ∧
      ConstantUnitNormalization (Modules K A) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (c : M ⟶ (towerLimit (Modules J A)).rightDerivedFunctor.obj
            ((towerDirect d).rightDerivedFunctor.obj V)),
        (limitAdjunction (Modules K A)).homEquiv
            (d.moduleFunctor.mapDerivedCategory.obj M) V
            ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
              ((towerAdjunction d).homEquiv
                ((Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M) V).symm
                (((limitAdjunction (Modules J A)).homEquiv M
                  ((towerDirect d).rightDerivedFunctor.obj V)).symm c)) =
          ((moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)).symm (c ≫ a.inv.app V)) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (b : (towerInverse d).mapDerivedCategory.obj Z ⟶ V)
          (j : (Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M ⟶ Z),
        (moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)
            ((limitAdjunction (Modules K A)).homEquiv
              (d.moduleFunctor.mapDerivedCategory.obj M) V
              ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
                (towerInverse d).mapDerivedCategory.map j ≫ b)) =
          (limitAdjunction (Modules J A)).unit.app M ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map j ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map
              ((towerAdjunction d).homEquiv Z V b) ≫ a.inv.app V) := by
  exact normalization d.moduleAdj

end Coefficients

end CategoryTheory.TowerLimitTransposeNormalization
