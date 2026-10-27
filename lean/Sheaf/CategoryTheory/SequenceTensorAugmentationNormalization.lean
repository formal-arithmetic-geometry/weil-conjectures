/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.CategoryTheory.DerivedTowerCounitProjections
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Sheaf.CategoryTheory.DerivedTowerCounitProjections
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-! # Normalized strict augmentations from derived adjunctions

The construction uses the whole constant-tower/derived-limit Hom equivalence.
It requires no exactness of countable products.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

/-- The exact constant functor and a K-injective derived limit have the normalized
cochain Hom correspondence. -/
private theorem constantLimitAdjunction
    {D : Type*} [Category D] [Abelian D] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ D)]
    (hres : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (q : X ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{d} D)
    (ζ : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (hRL : RL.IsRightDerivedFunctor ζ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ)))
    (hζ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ, I.IsKInjective → IsIso (ζ.app I)) :
    ∃ a : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ⊣ RL,
      (∀ Q : CochainComplex D ℤ,
        a.unit.app (DerivedCategory.Q.obj Q) ≫
            RL.map ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q) =
          DerivedCategory.Q.map
              (((constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⊣ lim).mapHomologicalComplex
                (.up ℤ)).unit.app Q) ≫
            ζ.app (((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
      (∀ (Q : CochainComplex D ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
        (f : ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj Q ⟶ T),
        a.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj T)
            ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q ≫
              DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
              (((constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⊣ lim).mapHomologicalComplex
              (.up ℤ)).homEquiv Q T f) ≫ ζ.app T) := by
  classical
  let := CategoryTheory.monicKInjectiveResolutions hres
  let Δ := (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D)
  let Δd := Δ.mapDerivedCategory
  let γ := Δ.mapDerivedCategoryFactors.hom
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ)
  let := hRL
  have hζ' (I : CochainComplex.KInjectives (ℕᵒᵖ ⥤ D)) : IsIso (ζ.app I.obj) :=
    hζ I.obj I.property
  let : (RL ⋙ Δd).IsRightDerivedFunctor
      (Functor.whiskerRight ζ Δd ≫ (Functor.associator _ _ _).hom) W :=
    (CochainComplex.KInjectives.localizerMorphism _)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure ζ hζ' Δd
  let : Δd.IsLeftDerivedFunctor γ (HomologicalComplex.quasiIso D (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ Δ.mapDerivedCategoryFactors
  let : (Δd ⋙ RL).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ RL)
      (HomologicalComplex.quasiIso D (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight Δ.mapDerivedCategoryFactors RL)
  let ac := (constLimAdj : Δ ⊣ lim).mapHomologicalComplex (.up ℤ)
  let a := ac.derived (HomologicalComplex.quasiIso D (.up ℤ)) W γ ζ
  have hu (Q : CochainComplex D ℤ) :
      a.unit.app (DerivedCategory.Q.obj Q) ≫ RL.map (γ.app Q) =
        DerivedCategory.Q.map (ac.unit.app Q) ≫
          ζ.app ((Δ.mapHomologicalComplex (.up ℤ)).obj Q) :=
    ac.derivedη_fac_app (HomologicalComplex.quasiIso D (.up ℤ)) γ ζ Q
  refine ⟨a, hu, ?_⟩
  intro Q T f
  rw [Adjunction.homEquiv_unit, RL.map_comp, ← Category.assoc, hu]
  have hn := ζ.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

/-- Extend the specified K-injective comparison to every complex by naturality. -/
private theorem comparisonOnAllComplexes
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (F : D ⥤ T) (U : D ⥤ E) (H : E ⥤ T)
    [F.Additive] [U.Additive] [H.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : F ≅ U ⋙ H)
    (R : DerivedCategory.{d} D ⥤ DerivedCategory.{d} T)
    (RH : DerivedCategory.{d} E ⥤ DerivedCategory.{d} T)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (ζ : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (c : R ≅ U.mapDerivedCategory ⋙ RH)
    (hD : ∀ X : CochainComplex D ℤ,
      ∃ (I : CochainComplex D ℤ) (a : X ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (hE : ∀ X : CochainComplex E ℤ,
      ∃ (I : CochainComplex E ℤ) (a : X ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (hc : ∀ (I : CochainComplex D ℤ), I.IsKInjective →
      ∀ (T' : CochainComplex E ℤ), T'.IsKInjective →
      ∀ (j : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ T') [QuasiIso j],
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RH.map (U.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map j) ≫
          ζ.app T' ≫ RH.map (inv (DerivedCategory.Q.map j))) :
    ∀ X : CochainComplex D ℤ,
      η.app X ≫ c.hom.app (DerivedCategory.Q.obj X) ≫
          RH.map (U.mapDerivedCategoryFactors.hom.app X) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app X) ≫
          ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj X) := by
  let eC : F.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex e (.up ℤ)
  let δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH) :=
    (Functor.isoWhiskerRight eC DerivedCategory.Q).hom ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ)) ζ ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight U.mapDerivedCategoryFactors.inv RH ≫
      (Functor.associator _ _ _).hom
  let η' : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH) :=
    η ≫ Functor.whiskerLeft DerivedCategory.Q c.hom
  have hδ (X : CochainComplex D ℤ) :
      δ.app X = DerivedCategory.Q.map (eC.hom.app X) ≫
        ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj X) ≫
        RH.map (U.mapDerivedCategoryFactors.inv.app X) := by
    simp only [δ, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hI (I : CochainComplex D ℤ) (hI : I.IsKInjective) : η'.app I = δ.app I := by
    obtain ⟨T', j, hT', hj⟩ := hE ((U.mapHomologicalComplex (.up ℤ)).obj I)
    let : QuasiIso j := hj
    have hh := hc I hI T' hT' j
    have hn := ζ.naturality j
    dsimp only [Functor.comp_map] at hn
    change η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
      RH.map (U.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map (eC.hom.app I) ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map j) ≫
        ζ.app T' ≫ RH.map (inv (DerivedCategory.Q.map j)) at hh
    rw [reassoc_of% hn, ← RH.map_comp, IsIso.hom_inv_id, RH.map_id,
      Category.comp_id] at hh
    apply (cancel_mono (RH.map (U.mapDerivedCategoryFactors.hom.app I))).mp
    change (η.app I ≫ c.hom.app (DerivedCategory.Q.obj I)) ≫ _ = δ.app I ≫ _
    rw [hδ]
    simp only [Category.assoc, ← RH.map_comp, Iso.inv_hom_id_app]
    erw [RH.map_id, Category.comp_id]
    exact hh
  have hall (X : CochainComplex D ℤ) : η'.app X = δ.app X := by
    obtain ⟨I, a, hi, ha⟩ := hD X
    let : QuasiIso a := ha
    apply (cancel_mono ((U.mapDerivedCategory ⋙ RH).map (DerivedCategory.Q.map a))).mp
    exact (η'.naturality a).symm.trans
      ((congrArg (fun f ↦ (F.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q).map a ≫ f) (hI I hi)).trans (δ.naturality a))
  intro X
  have hh := congrArg (fun f ↦ f ≫ RH.map (U.mapDerivedCategoryFactors.hom.app X))
    (hall X)
  change (η.app X ≫ c.hom.app (DerivedCategory.Q.obj X)) ≫ _ = δ.app X ≫ _ at hh
  rw [hδ] at hh
  simp only [Category.assoc, ← RH.map_comp, Iso.inv_hom_id_app] at hh
  erw [RH.map_id, Category.comp_id] at hh
  exact hh

/-- Taking mates of a natural unit gives a natural augmentation and recovers that unit. -/
private theorem augmentationOfUnit
    {D E T : Type*} [Category D] [Category E] [Category T]
    {L : D ⥤ E} {U : E ⥤ T} {Δ : D ⥤ T} {H : T ⥤ D}
    (d : L ⊣ U ⋙ H) (a : Δ ⊣ H) :
    ∃ b : Δ ⟶ L ⋙ U,
      (∀ X : D, d.unit.app X = a.unit.app X ≫ H.map (b.app X)) := by
  let b : Δ ⟶ L ⋙ U :=
    { app X := (a.homEquiv X (U.obj (L.obj X))).symm (d.unit.app X)
      naturality X Y f := by
        apply (a.homEquiv X (U.obj (L.obj Y))).injective
        dsimp only [Functor.comp_obj, Functor.comp_map]
        rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact d.unit.naturality f }
  refine ⟨b, fun X ↦ ?_⟩
  exact ((a.homEquiv X _).apply_symm_apply (d.unit.app X)).symm

/-- The ordinary augmentation is the mate of the ordinary tensor/limit unit. -/
private theorem ordinaryAugmentation
    {D E : Type*} [Category D] [Category E] [HasLimitsOfShape ℕᵒᵖ D]
    (G : D ⥤ E) (F : E ⥤ D) (U : E ⥤ (ℕᵒᵖ ⥤ D))
    (adj : G ⊣ F) (e : F ≅ U ⋙ lim) :
    ∃ b : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⟶ G ⋙ U,
      (∀ (M : D) (n : ℕᵒᵖ), (b.app M).app n =
        adj.unit.app M ≫ e.hom.app (G.obj M) ≫ limit.π (U.obj (G.obj M)) n) ∧
      (∀ M : D, constLimAdj.homEquiv M (U.obj (G.obj M)) (b.app M) =
        adj.unit.app M ≫ e.hom.app (G.obj M)) := by
  obtain ⟨b, hb⟩ := augmentationOfUnit (adj.ofNatIsoRight e) constLimAdj
  refine ⟨b, ?_, ?_⟩
  · intro M n
    have hh := congrArg (fun f ↦ f ≫ limit.π (U.obj (G.obj M)) n) (hb M)
    simpa [Adjunction.ofNatIsoRight, constLimAdj] using hh.symm
  · intro M
    exact (hb M).symm

/-- The mate of the derived unit is the localization of its ordinary strict mate. -/
private theorem augmentationNormalization
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ D)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive] (adj : G ⊣ F)
    (U : E ⥤ (ℕᵒᵖ ⥤ D)) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : F ≅ U ⋙ lim)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (hnorm : ∀ Q I (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
      dAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          η.app I)
    (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{d} D)
    (ζ : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (c : R ≅ U.mapDerivedCategory ⋙ RL)
    (hc : ∀ I : CochainComplex E ℤ,
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RL.map (U.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) ≫
          ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (beta : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⟶ G ⋙ U)
    (hbeta : ∀ M : D, constLimAdj.homEquiv M (U.obj (G.obj M)) (beta.app M) =
      adj.unit.app M ≫ e.hom.app (G.obj M))
    (a : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ⊣ RL)
    (ha : ∀ (Q : CochainComplex D ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
      (f : ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj Q ⟶ T),
      a.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj T)
          ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q ≫
            DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            (((constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⊣ lim).mapHomologicalComplex
              (.up ℤ)).homEquiv Q T f) ≫ ζ.app T) :
    ∃ b : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ⟶
        L ⋙ U.mapDerivedCategory,
      (∀ P : DerivedCategory.{d} D,
        (dAdj.ofNatIsoRight c).unit.app P = a.unit.app P ≫ RL.map (b.app P)) ∧
      (∀ Q : CochainComplex D ℤ,
        b.app (DerivedCategory.Q.obj Q) ≫ U.mapDerivedCategory.map (ε.app Q) ≫
            U.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
          (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) := by
  obtain ⟨b, hb⟩ := augmentationOfUnit (dAdj.ofNatIsoRight c) a
  refine ⟨b, hb, ?_⟩
  intro Q
  have hbc : ((constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).homEquiv Q
      ((U.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj Q))
      ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q) =
      (adj.mapHomologicalComplex (.up ℤ)).unit.app Q ≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) := by
    ext i
    change constLimAdj.homEquiv (Q.X i) (U.obj (G.obj (Q.X i)))
      (beta.app (Q.X i)) = adj.unit.app (Q.X i) ≫ e.hom.app (G.obj (Q.X i))
    exact hbeta (Q.X i)
  have hn := hnorm Q ((G.mapHomologicalComplex (.up ℤ)).obj Q) (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id] at hn
  rw [Adjunction.homEquiv_unit] at hn
  have hcn := c.hom.naturality (ε.app Q)
  dsimp only [Functor.comp_map] at hcn
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_unit, RL.map_comp, ← Category.assoc, ← hb]
  erw [ha]
  rw [hbc]
  erw [DerivedCategory.Q.map_comp]
  rw [Category.assoc, ← RL.map_comp]
  change (dAdj.unit.app _ ≫ c.hom.app _) ≫
    RL.map (U.mapDerivedCategory.map (ε.app Q) ≫ _) = _
  simp only [RL.map_comp, Category.assoc]
  rw [← reassoc_of% hcn, reassoc_of% hn, hc]
  rfl

/-- The limit of a strict augmentation is its whole adjoint transpose. -/
private theorem limitOfAugmentation
    {D E T : Type*} [Category D] [Category E] [Category T]
    {L : D ⥤ E} {U : E ⥤ T} {Δ : D ⥤ T} {H : T ⥤ D}
    (d : L ⊣ U ⋙ H) (a : Δ ⊣ H) (b : Δ ⟶ L ⋙ U)
    (hb : ∀ X : D, d.unit.app X = a.unit.app X ≫ H.map (b.app X))
    {P : D} {Y : T} (k : U.obj (L.obj P) ⟶ Y) (f : Δ.obj P ⟶ Y)
    (hk : b.app P ≫ k = f) :
    d.unit.app P ≫ H.map k = a.homEquiv P Y f := by
  rw [hb, Category.assoc, ← H.map_comp, hk]
  rfl

/-- A normalized derived adjunction induces the strict tensor augmentation.
Source: Stacks Project, Cohomology on Sites, Tags 07A6 and 0941;
Derived Categories, Tags 09T5 and 0FND.
(blueprint: lem-sf-sequence-tensor-augmentation-normalization)

Proof: take the ordinary constant/limit mate of the ordinary unit followed by `e`.
Derive the constant/limit adjunction using the supplied tower K-injective resolutions.
Its unit factorization and naturality give the normalized cochain Hom formula.
Extend the supplied comparison from K-injective systems to all complexes by resolving
both systems and towers, using naturality and cancelling localized quasi-isomorphisms.
Define the derived augmentation as the inverse tower-adjoint transpose of the
transported derived unit. To identify its localization, apply the tower Hom equivalence,
use the sequence Hom normalization at the identity, naturality of `c` at `ε`, and the
comparison just extended. The ordinary mate equation identifies the resulting cochain
map. Injectivity of the Hom equivalence gives equality of the whole augmentation.
Applying the same Hom formula to this equality gives the final total-limit identity.
`OrdinaryProperty` records any consequence of the component formula for the ordinary
mate. The predicates `P₁` and `P₂` are arbitrary: the derived calculation holds for all
complexes, so no flatness assumption is used here. -/
theorem normalizedTensorAugmentation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ D)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive] (adj : G ⊣ F)
    (U : E ⥤ (ℕᵒᵖ ⥤ D)) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : F ≅ U ⋙ lim)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (hnorm : ∀ Q I (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
      dAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          η.app I)
    (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{d} D)
    (ζ : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (c : R ≅ U.mapDerivedCategory ⋙ RL)
    (hresSystem : ∀ X : CochainComplex E ℤ,
      ∃ (I : CochainComplex E ℤ) (q : X ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hres : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (q : X ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hRL : RL.IsRightDerivedFunctor ζ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ)))
    (hζ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ, I.IsKInjective → IsIso (ζ.app I))
    (hc : ∀ (I : CochainComplex E ℤ), I.IsKInjective →
      ∀ (T : CochainComplex (ℕᵒᵖ ⥤ D) ℤ), T.IsKInjective →
      ∀ (j : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RL.map (U.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map
            (((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ)).map j) ≫
          ζ.app T ≫ RL.map (inv (DerivedCategory.Q.map j)))
    (OrdinaryProperty : ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⟶ G ⋙ U) → Prop)
    (hOrd : ∀ beta : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⟶ G ⋙ U,
      (∀ (M : D) (n : ℕᵒᵖ), (beta.app M).app n =
        adj.unit.app M ≫ e.hom.app (G.obj M) ≫ limit.π (U.obj (G.obj M)) n) →
      OrdinaryProperty beta)
    (P₁ P₂ : CochainComplex D ℤ → Prop) :
    ∃ (beta : (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D) ⟶ G ⋙ U)
      (towerAdj :
        (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ⊣ RL)
      (augmentation :
        (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ⟶
          L ⋙ U.mapDerivedCategory),
      OrdinaryProperty beta ∧
      (∀ Q : CochainComplex D ℤ,
        towerAdj.unit.app (DerivedCategory.Q.obj Q) ≫
            RL.map ((Functor.const ℕᵒᵖ :
              D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q) =
          DerivedCategory.Q.map
              (((constLimAdj :
                (Functor.const ℕᵒᵖ :
                  D ⥤ ℕᵒᵖ ⥤ D) ⊣
                    lim).mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
            ζ.app (((Functor.const ℕᵒᵖ :
              D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
      (∀ (P : DerivedCategory.{d} D),
        (dAdj.ofNatIsoRight c).unit.app P =
          towerAdj.unit.app P ≫ RL.map (augmentation.app P)) ∧
      (∀ (Q : CochainComplex D ℤ),
        P₁ Q → P₂ Q →
        (augmentation.app (DerivedCategory.Q.obj Q) ≫
            U.mapDerivedCategory.map (ε.app Q) ≫
            U.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
          (Functor.const ℕᵒᵖ :
            D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategoryFactors.hom.app Q ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ∧
        ((dAdj.ofNatIsoRight c).unit.app (DerivedCategory.Q.obj Q) ≫
            RL.map (U.mapDerivedCategory.map (ε.app Q) ≫
              U.mapDerivedCategoryFactors.hom.app
                ((G.mapHomologicalComplex (.up ℤ)).obj Q)) =
          DerivedCategory.Q.map
              (((constLimAdj :
                (Functor.const ℕᵒᵖ :
                  D ⥤ ℕᵒᵖ ⥤ D) ⊣
                    lim).mapHomologicalComplex (.up ℤ)).homEquiv Q
                ((U.mapHomologicalComplex (.up ℤ)).obj
                  ((G.mapHomologicalComplex (.up ℤ)).obj Q))
                ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ≫
            ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj
              ((G.mapHomologicalComplex (.up ℤ)).obj Q)))) := by
  have hcAll := comparisonOnAllComplexes F U
    (lim : (ℕᵒᵖ ⥤ D) ⥤ D) e R RL η ζ c hresSystem hres hc
  obtain ⟨beta, hbeta, hbetaAdj⟩ := ordinaryAugmentation G F U adj e
  obtain ⟨towerAdj, htowerUnit, htowerHom⟩ := constantLimitAdjunction hres RL ζ hRL hζ
  obtain ⟨augmentation, haugmentationUnit, haugmentation⟩ :=
    augmentationNormalization G F adj U e L R ε η dAdj hnorm RL ζ c
      hcAll beta hbetaAdj towerAdj htowerHom
  refine ⟨beta, towerAdj, augmentation, hOrd beta hbeta, htowerUnit, haugmentationUnit, ?_⟩
  intro Q _ _
  refine ⟨haugmentation Q, ?_⟩
  exact (limitOfAugmentation (dAdj.ofNatIsoRight c) towerAdj augmentation
    haugmentationUnit _ _ (haugmentation Q)).trans
      (htowerHom Q _ ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q))

end SheafOfModules.SequenceProjection
