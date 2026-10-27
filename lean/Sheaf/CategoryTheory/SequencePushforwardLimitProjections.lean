/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import all Sheaf.SixFunctors.ResolvingDerivedAdjunction
import all Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.SystemScalarCoherence
import Sheaf.CategoryTheory.SystemScalarGenerators
import Sheaf.CategoryTheory.SystemGrothendieck
import Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Total-limit projections and the sequence-projection adjunction

Source: Stacks Project, Cohomology on Sites, Tags 0D6E, 0941 and 07A6;
Derived Categories, Tag 09T5.
(blueprint: lem-coef-sequence-pushforward-limit-projections).

All functors act on the existing strict-system and module derived categories.
The initial existential data are exactly the normalized presentation provided by
`derivedAdjunction`. Index `n` denotes positive level `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance 10000] CategoryTheory.HasSheafify.isRightAdjoint

universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

private def exactCompFactors
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (F : D ⥤ E) (G : E ⥤ T) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun I ↦ G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app I) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj I)) (by
      intro I I' f
      change G.mapDerivedCategory.map (F.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
        (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I') ≫ _) = _
      erw [← Category.assoc, ← G.mapDerivedCategory.map_comp,
        F.mapDerivedCategoryFactors.hom.naturality f, G.mapDerivedCategory.map_comp,
        Category.assoc, G.mapDerivedCategoryFactors.hom.naturality
          ((F.mapHomologicalComplex (.up ℤ)).map f)]
      dsimp only [Functor.mapIso, Iso.trans, Functor.comp_map]
      rw [Category.assoc]
      try rfl)

private theorem exactCompComparison
    {D E T V : Type*} [Category D] [Category E] [Category T] [Category V]
    [Abelian D] [Abelian E] [Abelian T] [Abelian V]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    [HasDerivedCategory.{d} T] [HasDerivedCategory.{d} V]
    (F : D ⥤ E) (G : E ⥤ T) (H : D ⥤ V) (K : V ⥤ T)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (e : F ⋙ G ≅ H ⋙ K) :
    ∃ ξ : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
        H.mapDerivedCategory ⋙ K.mapDerivedCategory,
      ∀ I : CochainComplex D ℤ,
        ξ.hom.app (DerivedCategory.Q.obj I) ≫
            K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app I) ≫
            K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) =
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
            G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) := by
  let a := exactCompFactors F G
  let b := exactCompFactors H K
  let t := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) := ⟨a⟩
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
      ((H ⋙ K).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory) := ⟨b⟩
  let ξ := Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    _ _ (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory) t
  refine ⟨ξ, ?_⟩
  intro I
  have hh : ξ.hom.app (DerivedCategory.Q.obj I) ≫ b.hom.app I =
      a.hom.app I ≫ t.hom.app I := by
    dsimp only [ξ]
    rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    change (a.hom.app I ≫ t.hom.app I ≫ b.inv.app I) ≫ b.hom.app I = _
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [a, b, exactCompFactors, t, NatIso.ofComponents, Iso.trans,
    Functor.mapIso] at hh
  simp only [Category.assoc] at hh
  set_option backward.isDefEq.respectTransparency false in
    convert hh using 1 <;> rfl

private theorem leftDerivedPostcompose
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    (G : D ⥤ E) [G.Additive]
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso D (.up ℤ)))
    (P : CochainComplex D ℤ → Prop)
    (hres : ∀ X : CochainComplex D ℤ, ∃ (Y : CochainComplex D ℤ) (f : Y ⟶ X),
      P Y ∧ QuasiIso f)
    (hcomp : ∀ X, P X → IsIso (ε.app X))
    {T : Type*} [Category T] (H : DerivedCategory.{d} E ⥤ T) :
    ∃ ζ : DerivedCategory.Q ⋙ (L ⋙ H) ⟶
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ H,
      (L ⋙ H).IsLeftDerivedFunctor ζ (HomologicalComplex.quasiIso D (.up ℤ)) ∧
        ∀ X, ζ.app X = H.map (ε.app X) := by
  obtain ⟨εh, hh, he⟩ := exists_homotopy_leftDerived_comparison G L ε hL
  let q := HomotopyCategory.quotient D (.up ℤ)
  let W := HomotopyCategory.quasiIso D (.up ℤ)
  let F := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := E)
  let P' : Set (HomotopyCategory D (.up ℤ)) := fun X ↦ ∃ Y, P Y ∧ q.obj Y = X
  have hr : ∀ X, ∃ (Y : HomotopyCategory D (.up ℤ)) (f : Y ⟶ X), Y ∈ P' ∧ W f := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, f, hY, hf⟩ := hres X
    exact ⟨q.obj Y, q.map f, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hi : ∀ X Y (f : X ⟶ Y), X ∈ P' → Y ∈ P' → W f → IsIso (F.map f) := by
    rintro _ _ f ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf
    have := hcomp X hX
    have := hcomp Y hY
    change IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f))
    rw [← isIso_comp_left_iff (ε.app X)]
    erw [← ε.naturality f]
    change IsIso (L.map (DerivedCategory.Q.map f) ≫ ε.app Y)
    infer_instance
  let : W.HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated D).2.2.2.2.1
  have : H.PreservesRightKanExtension F DerivedCategory.Qh :=
    _root_.pro_absolute W DerivedCategory.Qh F H (fun X ↦ by
      obtain ⟨Y, _, hY, _⟩ := Functor.resolvingClass_essentialConstancy W F P' hr hi X
      exact ⟨Y, hY⟩)
  let := hh
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension L εh W
  let ζh := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh H
  have : (L ⋙ H).IsLeftDerivedFunctor ζh W := ⟨inferInstance⟩
  obtain ⟨ζ, hζ, hζapp⟩ := leftDerivedOnComplexes G H (L ⋙ H) ζh
  refine ⟨ζ, hζ, ?_⟩
  intro X
  rw [hζapp]
  simp only [ζh, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp, he]
  rfl

private theorem derivedExactAdjunction
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (a : G ⊣ F)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso D (.up ℤ)))
    (P : CochainComplex D ℤ → Prop)
    (hres : ∀ X : CochainComplex D ℤ, ∃ (Y : CochainComplex D ℤ) (f : Y ⟶ X),
      P Y ∧ QuasiIso f)
    (hcomp : ∀ X, P X → IsIso (ε.app X)) :
    ∃ dAdj : L ⊣ F.mapDerivedCategory,
      ∀ (X : CochainComplex D ℤ) (Y : CochainComplex E ℤ)
        (f : (G.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y),
        dAdj.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y)
            (ε.app X ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv X Y f) ≫
            F.mapDerivedCategoryFactors.inv.app Y := by
  obtain ⟨ζ, hζ, hζapp⟩ := leftDerivedPostcompose G L ε hL P hres hcomp F.mapDerivedCategory
  have hζeq : ζ = (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ε F.mapDerivedCategory := by
    ext X
    simpa only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp] using hζapp X
  rw [hζeq] at hζ
  let := hL
  let := hζ
  let β := F.mapDerivedCategoryFactors.inv
  have hF : F.mapDerivedCategory.IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso E (.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
  let := hF
  let t := (Functor.associator DerivedCategory.Q F.mapDerivedCategory L).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors L ≪≫
    Functor.associator _ _ _
  have : (F.mapDerivedCategory ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso E (.up ℤ)) :=
    by
      have he : t.inv = Functor.whiskerRight β L ≫
          (Functor.associator _ _ _).hom := by
        ext X
        simp [t, β]
      rw [← he]
      exact Functor.isRightDerivedFunctor_of_inverts _ _ t
  let ac := a.mapHomologicalComplex (.up ℤ)
  let dAdj := ac.derived (HomologicalComplex.quasiIso D (.up ℤ))
    (HomologicalComplex.quasiIso E (.up ℤ)) ε β
  refine ⟨dAdj, ?_⟩
  intro X Y f
  rw [Adjunction.homEquiv_unit, F.mapDerivedCategory.map_comp, ← Category.assoc]
  change ((ac.derivedη (HomologicalComplex.quasiIso D (.up ℤ)) ε β).app _ ≫
    F.mapDerivedCategory.map (ε.app X)) ≫ _ = _
  erw [ac.derivedη_fac_app (HomologicalComplex.quasiIso D (.up ℤ)) ε β X]
  have hn := F.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem leftDerivedEvaluate
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (G : D ⥤ E) [G.Additive]
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso D (.up ℤ)))
    (P : CochainComplex D ℤ → Prop)
    (hres : ∀ X : CochainComplex D ℤ, ∃ (Y : CochainComplex D ℤ) (f : Y ⟶ X),
      P Y ∧ QuasiIso f)
    (hcomp : ∀ X, P X → IsIso (ε.app X))
    (V : E ⥤ T) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V] :
    ∃ εV : DerivedCategory.Q ⋙ (L ⋙ V.mapDerivedCategory) ⟶
        (G ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      (L ⋙ V.mapDerivedCategory).IsLeftDerivedFunctor εV
        (HomologicalComplex.quasiIso D (.up ℤ)) ∧
      ∀ X, εV.app X = V.mapDerivedCategory.map (ε.app X) ≫
        V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj X) := by
  obtain ⟨ζ, hζ, hζapp⟩ := leftDerivedPostcompose G L ε hL P hres hcomp V.mapDerivedCategory
  let j : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ V.mapDerivedCategory ≅
      (G ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (G.mapHomologicalComplex (.up ℤ)) V.mapDerivedCategoryFactors
  let εV := ζ ≫ j.hom
  let := hζ
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension (L ⋙ V.mapDerivedCategory) ζ
    (HomologicalComplex.quasiIso D (.up ℤ))
  refine ⟨εV, ⟨?_⟩, ?_⟩
  · exact (Functor.isRightKanExtension_iff_of_iso₂ ζ εV j (Iso.refl _) (by simp [εV])).1
      inferInstance
  · intro X
    dsimp only [εV, NatTrans.comp_app]
    rw [hζapp]
    rfl


private theorem derivedEvaluatedAdjunction
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (G : D ⥤ E) [G.Additive]
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso D (.up ℤ)))
    (P : CochainComplex D ℤ → Prop)
    (hres : ∀ X : CochainComplex D ℤ, ∃ (Y : CochainComplex D ℤ) (f : Y ⟶ X),
      P Y ∧ QuasiIso f)
    (hcomp : ∀ X, P X → IsIso (ε.app X))
    (V : E ⥤ T) (S : T ⥤ D) [V.Additive] [S.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (a : G ⋙ V ⊣ S) :
    ∃ b : L ⋙ V.mapDerivedCategory ⊣ S.mapDerivedCategory,
      ∀ (Q : CochainComplex D ℤ) (K : CochainComplex T ℤ)
        (f : ((G ⋙ V).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
        b.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
          (V.mapDerivedCategory.map (ε.app Q) ≫
            V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫
            DerivedCategory.Q.map f) =
          DerivedCategory.Q.map (((a.mapHomologicalComplex (.up ℤ)).homEquiv Q K) f) ≫
            S.mapDerivedCategoryFactors.inv.app K := by
  obtain ⟨ζ, hζ, hζapp⟩ := leftDerivedEvaluate G L ε hL P hres hcomp V
  obtain ⟨b, hb⟩ := derivedExactAdjunction (G ⋙ V) S a (L ⋙ V.mapDerivedCategory)
    ζ hζ P hres (by
      intro Q hQ
      rw [hζapp]
      have : IsIso (ε.app Q) := hcomp Q hQ
      have : IsIso (V.mapDerivedCategory.map (ε.app Q)) := inferInstance
      set_option backward.isDefEq.respectTransparency false in
        exact IsIso.comp_isIso' inferInstance
          (NatIso.hom_app_isIso V.mapDerivedCategoryFactors
            ((G.mapHomologicalComplex (.up ℤ)).obj Q)))
  refine ⟨b, ?_⟩
  intro Q K f
  have hh := hb Q K f
  rw [hζapp] at hh
  erw [Category.assoc] at hh
  exact hh

private theorem adjunctionProjection
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (G : D ⥤ E) (F : E ⥤ D) (V : E ⥤ T) (S : T ⥤ D)
    [G.Additive] [F.Additive] [V.Additive] [S.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (a : G ⊣ F) (aV : G ⋙ V ⊣ S) (π : F ⟶ V ⋙ S)
    (ha : ∀ I : CochainComplex E ℤ,
      ((aV.mapHomologicalComplex (.up ℤ)).homEquiv
        ((F.mapHomologicalComplex (.up ℤ)).obj I)
        ((V.mapHomologicalComplex (.up ℤ)).obj I)
        ((V.mapHomologicalComplex (.up ℤ)).map
          ((a.mapHomologicalComplex (.up ℤ)).counit.app I))) =
        (NatTrans.mapHomologicalComplex π (.up ℤ)).app I)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (hR : R.IsRightDerivedFunctor η (HomologicalComplex.quasiIso E (.up ℤ)))
    (aD : L ⊣ R) (aVD : L ⋙ V.mapDerivedCategory ⊣ S.mapDerivedCategory)
    (hD : ∀ X I (f : (G.mapHomologicalComplex (.up ℤ)).obj X ⟶ I),
      aD.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj I)
        (ε.app X ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv X I f) ≫ η.app I)
    (hVD : ∀ X Y (f : ((G ⋙ V).mapHomologicalComplex (.up ℤ)).obj X ⟶ Y),
      aVD.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y)
        (V.mapDerivedCategory.map (ε.app X) ≫
          V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj X) ≫
          DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((aV.mapHomologicalComplex (.up ℤ)).homEquiv X Y f) ≫
          S.mapDerivedCategoryFactors.inv.app Y)
    (θ : R ⟶ V.mapDerivedCategory ⋙ S.mapDerivedCategory)
    (hθ : ∀ I : CochainComplex E ℤ,
      η.app I ≫ θ.app (DerivedCategory.Q.obj I) ≫
        S.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app I) ≫
        S.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app I)) :
    ∀ N : DerivedCategory.{d} E,
      V.mapDerivedCategory.map (aD.counit.app N) =
        (aVD.homEquiv (R.obj N) (V.mapDerivedCategory.obj N)).symm (θ.app N) := by
  let theta : R ⟶ V.mapDerivedCategory ⋙ S.mapDerivedCategory :=
    { app := fun N ↦ aVD.homEquiv (R.obj N) (V.mapDerivedCategory.obj N)
        (V.mapDerivedCategory.map (aD.counit.app N))
      naturality := by
        intro N N' f
        dsimp only [Functor.comp_map]
        rw [← aVD.homEquiv_naturality_left, ← aVD.homEquiv_naturality_right]
        congr 1
        change V.mapDerivedCategory.map (L.map (R.map f)) ≫
          V.mapDerivedCategory.map (aD.counit.app N') = _
        rw [← V.mapDerivedCategory.map_comp, ← V.mapDerivedCategory.map_comp]
        exact V.mapDerivedCategory.congr_map (aD.counit.naturality f) }
  have htheta : theta = θ := by
    let := hR
    apply R.rightDerived_ext η (HomologicalComplex.quasiIso E (.up ℤ))
    ext I
    change η.app I ≫ theta.app (DerivedCategory.Q.obj I) =
      η.app I ≫ θ.app (DerivedCategory.Q.obj I)
    apply (cancel_mono (S.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app I) ≫
      S.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj I))).1
    simp only [Category.assoc]
    rw [hθ]
    dsimp only [theta]
    rw [← Category.assoc]
    erw [← aVD.homEquiv_naturality_left]
    have hc : L.map (η.app I) ≫ aD.counit.app (DerivedCategory.Q.obj I) =
        ε.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
      apply (aD.homEquiv _ _).injective
      erw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply, hD]
      erw [← (a.mapHomologicalComplex (.up ℤ)).homEquiv_symm_id I,
        Equiv.apply_symm_apply]
      simp
    change aVD.homEquiv _ _ (V.mapDerivedCategory.map (L.map (η.app I)) ≫
      V.mapDerivedCategory.map (aD.counit.app (DerivedCategory.Q.obj I))) ≫ _ = _
    rw [← V.mapDerivedCategory.map_comp, hc, V.mapDerivedCategory.map_comp]
    rw [← Category.assoc]
    erw [← aVD.homEquiv_naturality_right]
    rw [Category.assoc]
    erw [V.mapDerivedCategoryFactors_hom_naturality]
    try simp only [Category.assoc]
    erw [hVD]
    rw [ha]
    rw [Category.assoc]
    erw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  intro N
  exact (aVD.homEquiv _ _).eq_symm_apply.mpr (congrArg (fun t ↦ t.app N) htheta)

private theorem unitProjection
    {D E T : Type*} [Category D] [Category E] [Category T]
    {L : D ⥤ E} {R : E ⥤ D} {V : E ⥤ T} {S : T ⥤ D}
    (a : L ⊣ R) (b : L ⋙ V ⊣ S) (θ : R ⟶ V ⋙ S)
    (hc : ∀ N, V.map (a.counit.app N) =
      (b.homEquiv (R.obj N) (V.obj N)).symm (θ.app N)) (P : D) :
    a.unit.app P ≫ θ.app (L.obj P) = b.unit.app P := by
  apply (b.homEquiv P ((L ⋙ V).obj P)).symm.injective
  rw [b.homEquiv_naturality_left_symm]
  change V.map (L.map (a.unit.app P)) ≫
    (b.homEquiv (R.obj (L.obj P)) (V.obj (L.obj P))).symm (θ.app (L.obj P)) = _
  rw [← hc, ← V.map_comp]
  change V.map (L.map (a.unit.app P) ≫ a.counit.app (L.obj P)) = _
  rw [a.left_triangle_components P]
  erw [V.map_id, Adjunction.homEquiv_symm_unit]
  rfl


private theorem inverseAdjunctProjection
    {D E T : Type*} [Category D] [Category E] [Category T]
    {L : D ⥤ E} {R : E ⥤ D} (a : L ⊣ R) (V : E ⥤ T)
    (P : D) (N : E) (h : P ⟶ R.obj N) :
    V.map ((a.homEquiv P N).symm h) =
      (L ⋙ V).map h ≫ V.map (a.counit.app N) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp]
  rfl

private theorem rightDerivedComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (F : C ⥤ E) (R S : D ⥤ E) (η : F ⟶ Q ⋙ R) (δ : F ⟶ Q ⋙ S)
    (hR : R.IsRightDerivedFunctor η W) (hS : S.IsRightDerivedFunctor δ W) :
    ∃ c : R ≅ S,
      ∀ I : C, η.app I ≫ c.hom.app (Q.obj I) = δ.app I := by
  let := hR
  let := hS
  let c := Functor.rightDerivedUnique R S η δ W
  have hc (I : C) : η.app I ≫ c.hom.app (Q.obj I) = δ.app I := by
    simpa only [c, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app R S η δ W (𝟙 F) I
  exact ⟨c, hc⟩

private theorem rightDerivedAfterExact
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T] [Abelian.HasKInjectiveResolutions D]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (F : D ⥤ T) (U : D ⥤ E) (H : E ⥤ T)
    [F.Additive] [U.Additive] [H.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (fComplex : F.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ))
    (RH : DerivedCategory.{d} E ⥤ DerivedCategory.{d} T)
    (ζ : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (hcompute : ∀ I : CochainComplex D ℤ, I.IsKInjective →
      IsIso (ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH),
      (∀ I : CochainComplex D ℤ, δ.app I = DerivedCategory.Q.map (fComplex.hom.app I) ≫
        ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
        RH.map (U.mapDerivedCategoryFactors.inv.app I)) ∧
      (U.mapDerivedCategory ⋙ RH).IsRightDerivedFunctor δ
        (HomologicalComplex.quasiIso D (.up ℤ)) := by
  let δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH) :=
    (Functor.isoWhiskerRight fComplex DerivedCategory.Q).hom ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ)) ζ ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight U.mapDerivedCategoryFactors.inv RH ≫
      (Functor.associator _ _ _).hom
  have hδ (I : CochainComplex D ℤ) (hI : I.IsKInjective) : IsIso (δ.app I) := by
    have := hcompute I hI
    dsimp only [δ, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  have hδR : (U.mapDerivedCategory ⋙ RH).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso (D) (.up ℤ)) := by
    apply (CategoryTheory.derives F).isRightDerivedFunctor_of_isIso δ
    intro I
    exact hδ I.obj I.property
  have hδapp (I : CochainComplex (D) ℤ) :
      δ.app I = DerivedCategory.Q.map (fComplex.hom.app I) ≫
        ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
        RH.map (U.mapDerivedCategoryFactors.inv.app I) := by
    simp only [δ, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  exact ⟨δ, hδapp, hδR⟩

private theorem transportProjectionChain
    {D : Type*} [Category D] {A B C X Y Z T : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (p : C ⟶ X)
    (q : X ⟶ Y) (r : Y ⟶ Z) (s : Z ⟶ T) (t : A ⟶ T)
    (hc : a ≫ b = c) (hp : c ≫ p ≫ q ≫ r ≫ s = t) :
    a ≫ b ≫ p ≫ q ≫ r ≫ s = t := by
  rw [← Category.assoc, hc, hp]

private theorem comparisonCancel
    {D E : Type*} [Category D] [Category E] (R : D ⥤ E)
    {X Y T : E} {V W : D} (a : X ⟶ Y) (b : Y ⟶ R.obj W)
    (c : X ⟶ R.obj W) (q : X ⟶ T) (z : T ⟶ R.obj V) (e : W ≅ V)
    (hab : a ≫ b = c) (hc : c = q ≫ z ≫ R.map e.inv) :
    a ≫ b ≫ R.map e.hom = q ≫ z := by
  rw [← Category.assoc, hab, hc, Category.assoc, Category.assoc,
    ← R.map_comp, e.inv_hom_id, R.map_id, Category.comp_id]

private theorem resolutionNaturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : C ⥤ E) (Q : C ⥤ D) (R : D ⥤ E) (ζ : H ⟶ Q ⋙ R)
    {X Y : C} (j : X ⟶ Y) [IsIso (Q.map j)] {Z : E} (q : Z ⟶ H.obj X) :
    q ≫ ζ.app X = q ≫ H.map j ≫ ζ.app Y ≫ R.map (inv (Q.map j)) := by
  rw [ζ.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← R.map_comp, IsIso.hom_inv_id, R.map_id]
  erw [Category.comp_id]

private theorem resolutionComparison
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    (F : D ⥤ T) (U : D ⥤ E) (H : E ⥤ T)
    [F.Additive] [U.Additive] [H.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (eC : F.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ))
    (R : DerivedCategory.{d} D ⥤ DerivedCategory.{d} T)
    (RH : DerivedCategory.{d} E ⥤ DerivedCategory.{d} T)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH))
    (ζ : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (c : R ≅ U.mapDerivedCategory ⋙ RH) (I : CochainComplex D ℤ)
    (hc : η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) = δ.app I)
    (hd : δ.app I =
      DerivedCategory.Q.map (eC.hom.app I) ≫
        ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
        RH.map (U.mapDerivedCategoryFactors.inv.app I))
    (T' : CochainComplex E ℤ) (j : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ T')
    [QuasiIso j] :
    η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
        RH.map (U.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map (eC.hom.app I) ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map j) ≫
        ζ.app T' ≫ RH.map (inv (DerivedCategory.Q.map j)) := by
  have hh := comparisonCancel RH (η.app I) (c.hom.app (DerivedCategory.Q.obj I))
    (δ.app I) (DerivedCategory.Q.map (eC.hom.app I))
    (ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (U.mapDerivedCategoryFactors.app I) hc hd
  exact hh.trans (resolutionNaturality _ DerivedCategory.Q RH ζ j _)

private theorem transportNormalized
    {D E : Type*} [Category D] [Category E]
    {F : D ⥤ E} {R S : E ⥤ D} (a : F ⊣ R) (e : R ≅ S)
    {X Z : D} {Y : E} (f : F.obj X ⟶ Y) (g : X ⟶ Z)
    (h : Z ⟶ R.obj Y) (k : Z ⟶ S.obj Y)
    (ha : a.homEquiv X Y f = g ≫ h) (hb : h ≫ e.hom.app Y = k) :
    (a.ofNatIsoRight e).homEquiv X Y f = g ≫ k := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, ha, Category.assoc, hb]

private theorem transportDerivedNormalization
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive] (a : G ⊣ F)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R S : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ S)
    (b : L ⊣ R) (c : R ≅ S)
    (hn : ∀ Q I (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
      b.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (ε.app Q ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫ η.app I)
    (hc : ∀ I, η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) = δ.app I) :
    ∀ Q I (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
      (b.ofNatIsoRight c).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (ε.app Q ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫ δ.app I := by
  intro Q I f
  exact transportNormalized b c _ _ _ _ (hn Q I f) (hc I)

private theorem cancel_projection
    {D E : Type*} [Category D] [Category E] {F G : D ⥤ E}
    (p : F ⟶ G) {X Y : D} (e : X ≅ Y) :
    F.map e.hom ≫ p.app Y ≫ G.map e.inv = p.app X := by
  rw [p.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]

private theorem complexProjection
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    (F H : D ⥤ E) (U : D ⥤ T) (V W : T ⥤ E)
    [F.Additive] [H.Additive] [U.Additive] [V.Additive] [W.Additive]
    (e : F ≅ U ⋙ V) (p : V ⟶ W) (a : U ⋙ W ≅ H) (q : F ⟶ H)
    (h : e.hom ≫ Functor.whiskerLeft U p ≫ a.hom = q)
    (I : CochainComplex D ℤ) :
    (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I ≫
      (NatTrans.mapHomologicalComplex p (.up ℤ)).app
        ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I =
        (NatTrans.mapHomologicalComplex q (.up ℤ)).app I := by
  apply HomologicalComplex.hom_ext
  intro i
  have hh := congrArg (fun t ↦ t.app (I.X i)) h
  change e.hom.app (I.X i) ≫ p.app (U.obj (I.X i)) ≫ a.hom.app (I.X i) =
    q.app (I.X i)
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectionAfterExact
    {D E T K : Type*} [Category D] [Category E] [Category T] [Category K]
    [Abelian D] [Abelian E] [Abelian T] [Abelian K]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    [HasDerivedCategory.{d} T] [HasDerivedCategory.{d} K]
    (F : D ⥤ T) (U : D ⥤ E) (H W : E ⥤ T) (V : D ⥤ K) (S : K ⥤ T)
    [F.Additive] [U.Additive] [H.Additive] [W.Additive] [V.Additive] [S.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ≅ U ⋙ H) (π : H ⟶ W) (a : U ⋙ W ≅ V ⋙ S) (q : F ⟶ V ⋙ S)
    (ho : e.hom ≫ Functor.whiskerLeft U π ≫ a.hom = q)
    (RH : DerivedCategory.{d} E ⥤ DerivedCategory.{d} T)
    (ζ : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RH))
    (hδapp : ∀ I : CochainComplex D ℤ,
      δ.app I = DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) ≫
        ζ.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
        RH.map (U.mapDerivedCategoryFactors.inv.app I))
    (p : RH ⟶ W.mapDerivedCategory)
    (hp0 : ∀ T : CochainComplex E ℤ,
      ζ.app T ≫ p.app (DerivedCategory.Q.obj T) ≫ W.mapDerivedCategoryFactors.hom.app T =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app T))
    (ξ : U.mapDerivedCategory ⋙ W.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ S.mapDerivedCategory)
    (hξ0 : ∀ I : CochainComplex D ℤ,
      ξ.hom.app (DerivedCategory.Q.obj I) ≫
        S.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app I) ≫
        S.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj I) =
      W.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app I) ≫
        W.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I))
    (I : CochainComplex D ℤ) :
    δ.app I ≫ p.app (U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
      ξ.hom.app (DerivedCategory.Q.obj I) ≫
      S.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app I) ≫
      S.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q (.up ℤ)).app I) := by
  have he := cancel_projection p (U.mapDerivedCategoryFactors.app I).symm
  dsimp only [Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv] at he
  have hp := hp0 ((U.mapHomologicalComplex (.up ℤ)).obj I)
  have hx := hξ0 I
  erw [hδapp, hx]
  simp only [Category.assoc]
  erw [reassoc_of% he]
  erw [reassoc_of% hp]
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  apply DerivedCategory.Q.congr_map
  exact complexProjection F (V ⋙ S)
    U H W
    e π a q ho I

private theorem derivedProjection
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E]
    (F V : D ⥤ E) [F.Additive] [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso D (.up ℤ)))
    (π : F ⟶ V) :
    ∃ p : RF ⟶ V.mapDerivedCategory, ∀ I : CochainComplex D ℤ,
      η.app I ≫ p.app (DerivedCategory.Q.obj I) ≫ V.mapDerivedCategoryFactors.hom.app I =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app I) := by
  let := hRF
  let τ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ V.mapDerivedCategory :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex π (.up ℤ)) DerivedCategory.Q ≫
      V.mapDerivedCategoryFactors.inv
  refine ⟨RF.rightDerivedDesc η (HomologicalComplex.quasiIso D (.up ℤ))
    V.mapDerivedCategory τ, ?_⟩
  intro I
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp [τ]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem ordinaryProjectionOnComplexes
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    (G : D ⥤ E) (F : E ⥤ D) (V : E ⥤ T) (S : T ⥤ D)
    [G.Additive] [F.Additive] [V.Additive] [S.Additive]
    (a : G ⊣ F) (b : G ⋙ V ⊣ S) (π : F ⟶ V ⋙ S)
    (h : ∀ N, b.homEquiv (F.obj N) (V.obj N) (V.map (a.counit.app N)) = π.app N)
    (I : CochainComplex E ℤ) :
    (b.mapHomologicalComplex (.up ℤ)).homEquiv
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
      ((V.mapHomologicalComplex (.up ℤ)).obj I)
      ((V.mapHomologicalComplex (.up ℤ)).map
        ((a.mapHomologicalComplex (.up ℤ)).counit.app I)) =
      (NatTrans.mapHomologicalComplex π (.up ℤ)).app I := by
  apply HomologicalComplex.hom_ext
  intro i
  exact h (I.X i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryLevel
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (G : Modules A ⥤ StrictRingSystem B)
    (e : ∀ (M : Modules A) (n : ℕ),
      (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
    (hmap : ∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
      (G.map f).app n ≫ (e M' n).hom =
        (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f)
    (n : ℕ) :
    ∃ a : G ⋙ systemEvaluation B n ⊣ restriction A B α n,
      ∀ (M : Modules A) (K : systemLevel B n)
        (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
        ((a.homEquiv M K).symm h).val.app V
            ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V) inferInstance b
            (h.val.app V x) := by
  obtain ⟨s⟩ := nonempty_systemScalarModel (α.app (op n))
  let k : G ⋙ systemEvaluation B n ≅ s.model.E :=
    NatIso.ofComponents (fun M ↦ e M n ≪≫ (eqToIso (s.model.obj_eq M)).symm) (by
      intro M M' f
      change (G.map f).app n ≫ ((e M' n).hom ≫ eqToHom (s.model.obj_eq M').symm) =
        ((e M n).hom ≫ eqToHom (s.model.obj_eq M).symm) ≫ s.model.E.map f
      rw [← Category.assoc, hmap, s.model.map_eq]
      simp)
  refine ⟨s.ordinaryAdj.ofNatIsoLeft k.symm, ?_⟩
  intro M K h V b x
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  change ((s.ordinaryAdj.homEquiv M K).symm h).val.app V
    ((k.hom.app M).val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x))) = _
  have ht : (k.hom.app M).val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
      systemModelTmul s.model M V b x := by
    change (eqToHom (s.model.obj_eq M).symm).val.app V
      ((e M n).hom.val.app V
        ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x))) = _
    have he := congrArg (fun f ↦ f.val.app V (tensorSection (α.app (op n)) M V b x))
      (e M n).inv_hom_id
    change (e M n).hom.val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) = _ at he
    rw [he]
    exact ((eqToHom (s.model.obj_eq M).symm).val.app V).hom.map_smul b _
  rw [ht, systemScalarModel_transpose_tmul, Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_hom_ext
    (A S : Sheaf J CommRingCat.{w}) (φ : A ⟶ S)
    (M : Modules A) (K : Modules S) (f g : changeOfRings φ M ⟶ K)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      f.val.app U (tensorSection φ M U 1 x) =
        g.val.app U (tensorSection φ M U 1 x)) : f = g := by
  obtain ⟨s⟩ := nonempty_systemScalarModel φ
  apply (cancel_epi (eqToHom (s.model.obj_eq M))).1
  apply systemScalarModel_hom_ext s M K
  intro U x
  have ht : (eqToHom (s.model.obj_eq M)).val.app U
      (systemModelTmul s.model M U 1 x) = tensorSection φ M U 1 x := by
    dsimp only [systemModelTmul, tensorSection]
    simp only [one_smul]
    change ((eqToHom (s.model.obj_eq M).symm ≫ eqToHom (s.model.obj_eq M)).val.app U)
      _ = _
    rw [eqToHom_trans]
    exact (@one_smul (S.obj.obj U) ((changeOfRings φ M).val.obj U) _ _ _).symm
  change f.val.app U ((eqToHom (s.model.obj_eq M)).val.app U _) =
    g.val.app U ((eqToHom (s.model.obj_eq M)).val.app U _)
  rw [ht]
  exact h U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryProjection
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
    (e : ∀ (M : Modules A) (n : ℕ),
      (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
    (π : ∀ (N : StrictRingSystem B) (n : ℕ),
      F.obj N ⟶ (restriction A B α n).obj (N.level n))
    (adj : G ⊣ F)
    (hsection : ∀ M N (h : M ⟶ F.obj N) n U b x,
      (((adj.homEquiv M N).symm h).app n).val.app U
          ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
        @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
          ((π N n).val.app U (h.val.app U x)))
    (n : ℕ) (a : G ⋙ systemEvaluation B n ⊣ restriction A B α n)
    (ha : ∀ M K (h : M ⟶ (restriction A B α n).obj K) U b x,
      ((a.homEquiv M K).symm h).val.app U
          ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
        @SMul.smul ((B.obj (op n)).obj.obj U) (K.val.obj U) inferInstance b
          (h.val.app U x)) (N : StrictRingSystem B) :
    a.homEquiv (F.obj N) (N.level n) ((adj.counit.app N).app n) = π N n := by
  apply (a.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (cancel_epi (e (F.obj N) n).inv).1
  apply tensor_hom_ext A (B.obj (op n)) (α.app (op n))
  intro U x
  change ((adj.counit.app N).app n).val.app U
      ((e (F.obj N) n).inv.val.app U _) = _
  have hc : adj.counit.app N = (adj.homEquiv (F.obj N) N).symm (𝟙 _) := by
    simp [Adjunction.homEquiv_counit]
  rw [hc]
  change _ = ((a.homEquiv (F.obj N) (N.level n)).symm (π N n)).val.app U
    ((e (F.obj N) n).inv.val.app U (tensorSection (α.app (op n)) (F.obj N) U 1 x))
  erw [hsection, ha]
  rfl

omit [EssentiallySmall.{w} C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryLimitIso
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (F : StrictRingSystem B ⥤ Modules A)
    (π : ∀ (N : StrictRingSystem B) (n : ℕ),
      F.obj N ⟶ (restriction A B α n).obj (N.level n))
    (hnat : ∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
      F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n))
    (hcone : ∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (x : (F.obj N).val.obj U),
      (π N m).val.app U x =
        (N.transition h).val.app U ((π N n).val.app U x))
    (hlim : ∀ (M : Modules A) (N : StrictRingSystem B)
      (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
      (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
        (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
      ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) :
    ∃ fLim : F ≅ RestrictedTowerResolution.directImage A B α,
      ∀ (N : StrictRingSystem B) (n : ℕ),
        fLim.hom.app N ≫ limit.π (RestrictedTowerResolution.tower A B α N) (op n) =
          π N n := by
  classical
  let cone (N : StrictRingSystem B) : Cone (RestrictedTowerResolution.tower A B α N) :=
    { pt := F.obj N
      π :=
        { app := fun n ↦ π N n.unop
          naturality := by
            intro n m h
            ext U x
            exact hcone N (leOfHom h.unop) U x } }
  have hc (N : StrictRingSystem B) : IsLimit (cone N) := by
    apply IsLimit.ofExistsUnique
    intro s
    obtain ⟨f, hf, hu⟩ := hlim s.pt N (fun n ↦ s.π.app (op n)) (by
      intro m n h U x
      exact (congrArg (fun f ↦ f.val.app U x) (s.w (homOfLE h).op)).symm)
    refine ⟨f, ?_, ?_⟩
    · intro n
      exact hf n.unop
    · intro g hg
      exact hu g (fun n ↦ hg (op n))
  let e (N : StrictRingSystem B) := (hc N).conePointUniqueUpToIso
    (limit.isLimit (RestrictedTowerResolution.tower A B α N))
  have he (N : StrictRingSystem B) (n : ℕ) :
      (e N).hom ≫ limit.π (RestrictedTowerResolution.tower A B α N) (op n) =
        π N n := by
    exact (limit.isLimit _).fac (cone N) (op n)
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro N N' f
  apply limit.hom_ext
  intro n
  obtain ⟨n⟩ := n
  change (F.map f ≫ (e N').hom) ≫ limit.π _ (op n) =
    ((e N).hom ≫ limMap ((RestrictedTowerResolution.restrictionFunctor A B α).map f)) ≫
      limit.π _ (op n)
  rw [Category.assoc, he, Category.assoc, limMap_π, ← Category.assoc, he]
  exact hnat f n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryRestrictionData
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)]
    (F : StrictRingSystem B ⥤ Modules A)
    (π : ∀ (N : StrictRingSystem B) (n : ℕ),
      F.obj N ⟶ (restriction A B α n).obj (N.level n))
    (hnat : ∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
      F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n))
    (hcone : ∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (x : (F.obj N).val.obj U),
      (π N m).val.app U x =
        (N.transition h).val.app U ((π N n).val.app U x))
    (hlim : ∀ (M : Modules A) (N : StrictRingSystem B)
      (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
      (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
        (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
      ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) :
    ∃ (U0 : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A))
      (_ : U0.Additive) (_ : PreservesFiniteLimits U0)
      (_ : PreservesFiniteColimits U0)
      (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
        (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n))
      (uEval : ∀ n : ℕ,
        U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
          systemEvaluation B n ⋙ restriction A B α n)
      (πOrd : ∀ n : ℕ, F ⟶ systemEvaluation B n ⋙ restriction A B α n)
      (fLim : F ≅ U0 ⋙ (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)),
    (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
      (U0.map f).app (op n) ≫ eqToHom (uObj N' n) =
        eqToHom (uObj N n) ≫ (restriction A B α n).map (f.app n)) ∧
    (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
      (V : Cᵒᵖ) (x : (N.level n).val.obj V),
      ((U0.obj N).map (homOfLE h).op).val.app V
          ((eqToHom (uObj N n).symm).val.app V x) =
        (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x)) ∧
    (∀ (N : StrictRingSystem B) (n : ℕ),
      (uEval n).hom.app N = eqToHom (uObj N n)) ∧
    (∀ (N : StrictRingSystem B) (n : ℕ), (πOrd n).app N = π N n) ∧
    (∀ (N : StrictRingSystem B) (n : ℕ),
      fLim.hom.app N ≫ limit.π (U0.obj N) (op n) ≫ (uEval n).hom.app N = π N n) ∧
    (∀ n : ℕ, fLim.hom ≫ Functor.whiskerLeft U0 (lim.π (op n)) ≫
      (uEval n).hom = πOrd n) ∧
    (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
      ∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
      ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
        QuasiIso (((lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex
          (.up ℤ)).map j)) := by
  classical
  let U0 := RestrictedTowerResolution.restrictionFunctor A B α
  obtain ⟨hUlim, hUcolim⟩ := RestrictedTowerResolution.restrictionFunctor_exact A B α
  let : PreservesFiniteLimits U0 := hUlim
  let : PreservesFiniteColimits U0 := hUcolim
  obtain ⟨fLim, hfLim⟩ := ordinaryLimitIso A B α F π hnat hcone hlim
  let uObj (N : StrictRingSystem B) (n : ℕ) :
      (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n) := rfl
  let uEval (n : ℕ) : U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
      systemEvaluation B n ⋙ restriction A B α n :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro N N' f
      change (restriction A B α n).map (f.app n) ≫ 𝟙 _ =
        𝟙 _ ≫ (restriction A B α n).map (f.app n)
      simp only [Category.id_comp, Category.comp_id])
  let πOrd (n : ℕ) : F ⟶ systemEvaluation B n ⋙ restriction A B α n :=
    { app := fun N ↦ π N n
      naturality := fun _ _ f ↦ hnat f n }
  refine ⟨U0, inferInstance, hUlim, hUcolim, uObj, uEval, πOrd, fLim, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N N' f n
    change (restriction A B α n).map (f.app n) ≫ 𝟙 _ =
      𝟙 _ ≫ (restriction A B α n).map (f.app n)
    simp
  · intro N m n h V x
    rfl
  · intro N n
    rfl
  · intro N n
    rfl
  · intro N n
    change fLim.hom.app N ≫ limit.π _ (op n) ≫ 𝟙 _ = π N n
    rw [Category.comp_id]
    exact hfLim N n
  · intro n
    apply NatTrans.ext
    funext N
    change fLim.hom.app N ≫ limit.π _ (op n) ≫ 𝟙 _ = π N n
    rw [Category.comp_id]
    exact hfLim N n
  · intro I hI T hT j hj
    let : I.IsKInjective := hI
    let : T.IsKInjective := hT
    let : QuasiIso j := hj
    exact (RestrictedTowerResolution.acyclicity A B α (𝟙 I) j).1

/-- Projection, resolution and adjunction normalization for a derived inverse limit.
This predicate is exactly the displayed conjunction of normalized equations; it fixes
all functors and comparisons before stating those equations, so concrete uses do not
re-elaborate the abelian and localization structures in each clause.
Source: Stacks 0D6E, 0941 and 07A6.
(blueprint: lem-coef-sequence-pushforward-limit-projections). -/
def derivedLimitProperties
    {D E T : Type*} {K : ℕ → Type*}
    [Category D] [Category E] [Category T] [∀ n, Category (K n)]
    [Abelian D] [Abelian E] [Abelian T] [∀ n, Abelian (K n)]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    [∀ n : ℕ, HasDerivedCategory.{d} (K n)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive]
    (U0 : E ⥤ T) (H : T ⥤ D) [U0.Additive] [H.PreservesZeroMorphisms]
    [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
    (W : ℕ → (T ⥤ D)) (V : ∀ n, E ⥤ K n) (S : ∀ n, K n ⥤ D)
    [∀ n, (W n).Additive] [∀ n, (V n).Additive] [∀ n, (S n).Additive]
    [∀ n, PreservesFiniteLimits (W n)] [∀ n, PreservesFiniteColimits (W n)]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
    (uEval : ∀ n, U0 ⋙ W n ≅ V n ⋙ S n)
    (πOrd : ∀ n, F ⟶ V n ⋙ S n) (fLim : F ≅ U0 ⋙ H) (pOrd : ∀ n, H ⟶ W n)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (RL : DerivedCategory.{d} T ⥤ DerivedCategory.{d} D)
    (etaLim : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (LevelProperty : (∀ n, G ⋙ V n ⊣ S n) → Prop)
    (piLim : ∀ n, RL ⟶ (W n).mapDerivedCategory)
      (xi : ∀ n, U0.mapDerivedCategory ⋙ (W n).mapDerivedCategory ≅
        (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory)
      (c : R ≅ U0.mapDerivedCategory ⋙ RL)
      (levelAdj : ∀ n, G ⋙ V n ⊣ S n)
      (derivedLevelAdj : ∀ n,
        L ⋙ (V n).mapDerivedCategory ⊣ (S n).mapDerivedCategory) : Prop :=
    (∀ (T : CochainComplex T ℤ) (n : ℕ),
      etaLim.app T ≫ (piLim n).app (DerivedCategory.Q.obj T) ≫
          (W n).mapDerivedCategoryFactors.hom.app T =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pOrd n) (.up ℤ)).app T)) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        (W n).mapDerivedCategory.map
            (U0.mapDerivedCategoryFactors.hom.app I) ≫
          (W n).mapDerivedCategoryFactors.hom.app
            ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (uEval n) (.up ℤ)).hom.app I)) ∧
    (∀ (I : CochainComplex E ℤ), I.IsKInjective →
      ∀ (T : CochainComplex T ℤ), T.IsKInjective →
      ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      QuasiIso ((H.mapHomologicalComplex
        (.up ℤ)).map j) ∧
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RL.map (U0.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex fLim (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map
            ((H.mapHomologicalComplex
              (.up ℤ)).map j) ≫
          etaLim.app T ≫ RL.map (inv (DerivedCategory.Q.map j))) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)) ∧
    LevelProperty levelAdj ∧
    (∀ (n : ℕ) (Q : CochainComplex D ℤ)
      (K : CochainComplex (K n) ℤ)
      (f : ((G ⋙ V n).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
      (derivedLevelAdj n).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
          ((V n).mapDerivedCategory.map (ε.app Q) ≫
            (V n).mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            (((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
          (S n).mapDerivedCategoryFactors.inv.app K) ∧
    (∀ (P : DerivedCategory.{d} D) (n : ℕ),
      (dAdj.ofNatIsoRight c).unit.app P ≫
          (piLim n).app (U0.mapDerivedCategory.obj (L.obj P)) ≫
          (xi n).hom.app (L.obj P) = (derivedLevelAdj n).unit.app P) ∧
    (∀ (N : DerivedCategory.{d} E) (n : ℕ),
      (V n).mapDerivedCategory.map
          ((dAdj.ofNatIsoRight c).counit.app N) =
        ((derivedLevelAdj n).homEquiv
          ((U0.mapDerivedCategory ⋙ RL).obj N)
          ((V n).mapDerivedCategory.obj N)).symm
            ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N)) ∧
    (∀ (P : DerivedCategory.{d} D)
      (N : DerivedCategory.{d} E)
      (h : P ⟶ (U0.mapDerivedCategory ⋙ RL).obj N) (n : ℕ),
      (V n).mapDerivedCategory.map
          (((dAdj.ofNatIsoRight c).homEquiv P N).symm h) =
        (L ⋙ (V n).mapDerivedCategory).map h ≫
          (V n).mapDerivedCategory.map
            ((dAdj.ofNatIsoRight c).counit.app N)) ∧
    (∀ (P : DerivedCategory.{d} D),
      L.map ((dAdj.ofNatIsoRight c).unit.app P) ≫
        (dAdj.ofNatIsoRight c).counit.app (L.obj P) = 𝟙 (L.obj P)) ∧
    (∀ (N : DerivedCategory.{d} E),
      (dAdj.ofNatIsoRight c).unit.app ((U0.mapDerivedCategory ⋙ RL).obj N) ≫
        (U0.mapDerivedCategory ⋙ RL).map ((dAdj.ofNatIsoRight c).counit.app N) =
          𝟙 ((U0.mapDerivedCategory ⋙ RL).obj N))

/-- Exact restriction followed by a derived limit preserves normalized adjunction projections. -/
private theorem derivedLimitAdjunctionAssembly
    {D E T : Type*} {K : ℕ → Type*}
    [Category D] [Category E] [Category T] [∀ n, Category (K n)]
    [Abelian D] [Abelian E] [Abelian T] [∀ n, Abelian (K n)]
    [Abelian.HasKInjectiveResolutions E]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    [∀ n : ℕ, HasDerivedCategory.{d} (K n)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive] (adj : G ⊣ F)
    (U0 : E ⥤ T) (H : T ⥤ D) [U0.Additive] [H.Additive]
    [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
    (W : ℕ → (T ⥤ D)) (V : ∀ n, E ⥤ K n) (S : ∀ n, K n ⥤ D)
    [∀ n, (W n).Additive] [∀ n, (V n).Additive] [∀ n, (S n).Additive]
    [∀ n, PreservesFiniteLimits (W n)] [∀ n, PreservesFiniteColimits (W n)]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
    (uEval : ∀ n, U0 ⋙ W n ≅ V n ⋙ S n)
    (πOrd : ∀ n, F ⟶ V n ⋙ S n) (fLim : F ≅ U0 ⋙ H) (pOrd : ∀ n, H ⟶ W n)
    (ho : ∀ n, fLim.hom ≫ Functor.whiskerLeft U0 (pOrd n) ≫ (uEval n).hom = πOrd n)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso D (.up ℤ)))
    (hR : R.IsRightDerivedFunctor η (HomologicalComplex.quasiIso E (.up ℤ)))
    (hnorm : ∀ Q I (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
      dAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (ε.app Q ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫ η.app I)
    (RL : DerivedCategory.{d} T ⥤ DerivedCategory.{d} D)
    (etaLim : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (hRL : RL.IsRightDerivedFunctor etaLim (HomologicalComplex.quasiIso T (.up ℤ)))
    (hηLim : ∀ T' : CochainComplex T ℤ, T'.IsKInjective → IsIso (etaLim.app T'))
    (hresLim : ∀ X : CochainComplex T ℤ,
      ∃ (T' : CochainComplex T ℤ) (j : X ⟶ T'), T'.IsKInjective ∧ QuasiIso j)
    (hacyclic : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      ∀ T' : CochainComplex T ℤ, T'.IsKInjective →
      ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T') [QuasiIso j],
      QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map j))
    (levelAdj : ∀ n, G ⋙ V n ⊣ S n)
    (ha : ∀ n (I : CochainComplex E ℤ),
      ((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv
        ((F.mapHomologicalComplex (.up ℤ)).obj I)
        (((V n).mapHomologicalComplex (.up ℤ)).obj I)
        (((V n).mapHomologicalComplex (.up ℤ)).map
          ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)) =
        (NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)
    (P : CochainComplex D ℤ → Prop)
    (hflatRes : ∀ X : CochainComplex D ℤ,
      ∃ (Q : CochainComplex D ℤ) (q : Q ⟶ X), P Q ∧ QuasiIso q)
    (hcomp : ∀ Q, P Q → IsIso (ε.app Q))
    (LevelProperty : (∀ n, G ⋙ V n ⊣ S n) → Prop)
    (hlevel : LevelProperty levelAdj)
    : ∃ (piLim : ∀ n, RL ⟶ (W n).mapDerivedCategory)
      (xi : ∀ n, U0.mapDerivedCategory ⋙ (W n).mapDerivedCategory ≅
        (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory)
      (c : R ≅ U0.mapDerivedCategory ⋙ RL)
      (derivedLevelAdj : ∀ n,
        L ⋙ (V n).mapDerivedCategory ⊣ (S n).mapDerivedCategory),
      derivedLimitProperties G F U0 H W V S uEval πOrd fLim pOrd
        L R ε η dAdj RL etaLim LevelProperty piLim xi c levelAdj derivedLevelAdj := by
  classical
  choose piLim hpiLim using fun n : ℕ ↦
    derivedProjection H
      (W n) RL etaLim hRL (pOrd n)
  let fComplex : F.mapHomologicalComplex (.up ℤ) ≅
      U0.mapHomologicalComplex (.up ℤ) ⋙
        H.mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex fLim (.up ℤ)
  have hcompute (I : CochainComplex E ℤ) (hI : I.IsKInjective) :
      IsIso (etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj I)) := by
    obtain ⟨T, j, hT, hj⟩ := hresLim ((U0.mapHomologicalComplex (.up ℤ)).obj I)
    let : I.IsKInjective := hI
    let : T.IsKInjective := hT
    let : QuasiIso j := hj
    have hacyc := hacyclic I hI T hT j
    have : QuasiIso ((H.mapHomologicalComplex
        (.up ℤ)).map j) := hacyc
    have : IsIso (etaLim.app T) := hηLim T hT
    have hn := etaLim.naturality j
    dsimp only [Functor.comp_map] at hn
    have : IsIso (etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
        RL.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    have : IsIso (etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj I)) :=
      IsIso.of_isIso_comp_right _ (RL.map (DerivedCategory.Q.map j))
    infer_instance
  obtain ⟨δ, hδapp, hδR⟩ := rightDerivedAfterExact F U0
    H fComplex RL etaLim hcompute
  obtain ⟨c, hc⟩ := rightDerivedComparison
    (C := CochainComplex E ℤ)
    (D := DerivedCategory.{d} E)
    (E := DerivedCategory.{d} D) DerivedCategory.Q
    (HomologicalComplex.quasiIso E (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) R
    (U0.mapDerivedCategory ⋙ RL) η δ hR hδR
  choose xi hxi using fun n : ℕ ↦ exactCompComparison U0
    (W n)
    (V n) (S n) (uEval n)
  choose derivedLevelAdj hderivedLevel using fun n : ℕ ↦
    derivedEvaluatedAdjunction G L ε hL P hflatRes hcomp
      (V n) (S n) (levelAdj n)
  refine ⟨piLim, xi, c, derivedLevelAdj, ?_⟩
  have hprojδ (I : CochainComplex E ℤ) (n : ℕ) :
      δ.app I ≫ (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
        (xi n).hom.app (DerivedCategory.Q.obj I) ≫
        (S n).mapDerivedCategory.map
          ((V n).mapDerivedCategoryFactors.hom.app I) ≫
        (S n).mapDerivedCategoryFactors.hom.app
          (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I) := by
    exact projectionAfterExact F U0 H
      (W n)
      (V n) (S n) fLim (pOrd n)
      (uEval n) (πOrd n) (ho n) RL etaLim δ hδapp (piLim n)
      (hpiLim n) (xi n) (hxi n) I
  let d := dAdj.ofNatIsoRight c
  have hd := transportDerivedNormalization G F adj L R
    (U0.mapDerivedCategory ⋙ RL) ε η δ dAdj c hnorm hc
  let θ (n : ℕ) : U0.mapDerivedCategory ⋙ RL ⟶
      (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory :=
    Functor.whiskerLeft U0.mapDerivedCategory (piLim n) ≫ (xi n).hom
  have hcounit (N : DerivedCategory.{d} E) (n : ℕ) :
      (V n).mapDerivedCategory.map (d.counit.app N) =
        ((derivedLevelAdj n).homEquiv ((U0.mapDerivedCategory ⋙ RL).obj N)
          ((V n).mapDerivedCategory.obj N)).symm
          ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N) := by
    apply adjunctionProjection G F (V n) (S n)
      adj (levelAdj n) (πOrd n) ?_ L (U0.mapDerivedCategory ⋙ RL) ε δ hδR
      d (derivedLevelAdj n) hd (hderivedLevel n) (θ n) (by
        intro I
        simpa only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
          using hprojδ I n) N
    exact ha n
  refine And.intro (fun T n ↦ hpiLim n T) ?_
  refine And.intro (fun I n ↦ hxi n I) ?_
  refine And.intro ?_ ?_
  · intro I hI T hT j hj
    let : I.IsKInjective := hI
    let : T.IsKInjective := hT
    let : QuasiIso j := hj
    refine ⟨hacyclic I hI T hT j, ?_⟩
    have hh := resolutionComparison F U0
      H fComplex R RL η δ etaLim c I
      (hc I) (hδapp I) T j
    dsimp only [fComplex] at hh
    exact hh
  refine And.intro ?_ ?_
  · intro I n
    exact transportProjectionChain _ _ _ _ _ _ _ _ (hc I) (hprojδ I n)
  refine And.intro hlevel ?_
  refine And.intro ?_ ?_
  · exact hderivedLevel
  refine And.intro ?_ ?_
  · intro Q n
    have hh := unitProjection
      (L := L) (R := U0.mapDerivedCategory ⋙ RL)
      (V := (V n).mapDerivedCategory)
      (S := (S n).mapDerivedCategory)
      d (derivedLevelAdj n) (θ n) (by
      intro N
      simpa only [θ, NatTrans.comp_app, Functor.whiskerLeft_app]
        using hcounit N n) Q
    simpa only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using hh
  refine And.intro ?_ ?_
  · exact hcounit
  refine And.intro ?_ ?_
  · intro Q N h n
    exact inverseAdjunctProjection d (V n).mapDerivedCategory Q N h
  refine And.intro ?_ ?_
  · exact d.left_triangle_components
  exact d.right_triangle_components


attribute [local irreducible] _root_.instCategoryDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


-- The statement retains all normalized presentation clauses of the sequence adjunction.
set_option maxHeartbeats 200000 in
-- Retain all normalization clauses in the full comparison statement.
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison with restricted total inverse limit preserves its actual
projections and transports the sequence-projection adjunction with the stated level formulas.
Source: Stacks 0D6E, 0941, 07A6 and derived.tex 09T5
(blueprint: lem-coef-sequence-pushforward-limit-projections).

Proof plan:
1. Take the normalized ordinary and derived data of
lem-coef-sequence-projection-derived-adjunction (`derivedAdjunction`), using
lem-pur-system-ringed-sequence-site (`strictSystemSequenceEquivalence`). Factor the
ringed projection through the constant ring sequence. Termwise scalar restriction U0
is exact: kernels and sheafified cokernels are unchanged on underlying abelian sheaves
(def-pc-sheaf-restrict-scalars). Its level identifications have the prescribed section maps.
2. Use prop-pur-kinjective-resolutions-exist on both sequence ringed sites. Apply
lem-weil-pbc-ringed-topoi-derived-pushforward-composition to the factorization, and
lem-weil-pbc-ringed-strict-tower-homotopy-limit to the projection with constant coefficients.
For K-injective I and a K-injective resolution j:U0(I) to T, the comparison is the class
of lim(j), under the displayed universal-unit identifications; lim(j) is a quasi-isomorphism.
3. The equality pr_n(lim(j)) = j_n(pr_n) proves that this comparison preserves the actual
limit projections. The equations with etaLim specify those projections by the ordinary
termwise projections, including on arbitrary complex representatives.
4. Apply lem-weil-pbc-ringed-topoi-module-adjunction at each level. Its scalar transpose
sends a map h to b tensor x mapped to b times h(x). Restriction is exact. Use
lem-pc-kflat-resolution, lem-pur-derived-change-of-rings and
lem-pur-resolving-class-derived-adjunction to derive this adjunction. Its displayed
chain-map equation fixes the canonical transpose for arbitrary targets; K-flat
resolutions extend it to fractions. The level of L is derived scalar extension by the
simultaneous K-flat description in the sequence-projection dependency.
5. Transport derivedAdj along c by Adjunction.ofNatIsoRight. Its unit is the old unit
followed by c, and its counit is L(c inverse) followed by the old counit. Naturality and
the old triangles give both triangle identities as equalities of actual derived maps.
6. On a flat-term K-flat Q, the old unit sends x to (a_n(x tensor 1))_n for a system
resolution a. Step 3 cancels a_n after projection; step 4 identifies the resulting map
with the reduction unit at level n.
7. For a K-injective system I and a K-flat resolution q:Q to lim(U0(I)), the old counit
has components b tensor x mapped to b times pr_n(q(x)). Step 4 gives adjunct pr_n,
and step 3 identifies it with pi_n composed with c. Precomposing with L(c inverse)
gives exactly pi_n. Neither U0(I) nor its levels are assumed K-injective.
8. The inverse transported Hom bijection sends h to L(h) followed by the counit.
Evaluation is functorial and L evaluated at n is scalar extension. This gives the final
component formula, naturally in both arguments, and the two actual triangle equations. -/
theorem pushforwardLimitProjections
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A)]
    [∀ n : ℕ, HasDerivedCategory.{d} (systemLevel B n)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) ∧
        ∃ (U0 : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A))
          (_ : U0.Additive) (_ : PreservesFiniteLimits U0)
          (_ : PreservesFiniteColimits U0)
          (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
            (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n))
          (uEval : ∀ n : ℕ,
            U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
              systemEvaluation B n ⋙ restriction A B α n)
          (πOrd : ∀ n : ℕ, F ⟶ systemEvaluation B n ⋙ restriction A B α n)
          (fLim : F ≅ U0 ⋙ (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A))
          (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A) ⥤ DerivedCategory.{d} (Modules A))
          (etaLim : (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
          (piLim : ∀ n : ℕ, RL ⟶
            ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory)
          (xi : ∀ n : ℕ,
            U0.mapDerivedCategory ⋙
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory ≅
              (systemEvaluation B n).mapDerivedCategory ⋙
                (restriction A B α n).mapDerivedCategory)
          (c : R ≅ U0.mapDerivedCategory ⋙ RL)
          (levelAdj : ∀ n : ℕ, G ⋙ systemEvaluation B n ⊣ restriction A B α n)
          (derivedLevelAdj : ∀ n : ℕ,
            L ⋙ (systemEvaluation B n).mapDerivedCategory ⊣
              (restriction A B α n).mapDerivedCategory),
          (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
            (U0.map f).app (op n) ≫ eqToHom (uObj N' n) =
              eqToHom (uObj N n) ≫ (restriction A B α n).map (f.app n)) ∧
          (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
            (V : Cᵒᵖ) (x : (N.level n).val.obj V),
            ((U0.obj N).map (homOfLE h).op).val.app V
                ((eqToHom (uObj N n).symm).val.app V x) =
              (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            (uEval n).hom.app N = eqToHom (uObj N n)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ), (πOrd n).app N = π N n) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            fLim.hom.app N ≫ limit.π (U0.obj N) (op n) ≫ (uEval n).hom.app N = π N n) ∧
          RL.IsRightDerivedFunctor etaLim
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules A) (.up ℤ)) ∧
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            IsIso (etaLim.app T)) ∧
          derivedLimitProperties G F U0 (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)
            (fun n ↦ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))
            (systemEvaluation B) (restriction A B α) uEval πOrd fLim
            (fun n ↦ lim.π (op n)) L R ε η derivedAdj RL etaLim
            (fun levelAdj ↦ ∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V)
                (by
                  set_option backward.isDefEq.respectTransparency.types false in
                    exact inferInstance) b
                (h.val.app V x))
            piLim xi c levelAdj derivedLevelAdj :=
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    by
  classical
  let : HasWeakSheafify J AddCommGrpCat.{w} := HasSheafify.isRightAdjoint
  let : ∀ n : ℕ, PreservesFiniteLimits (systemEvaluation B n) := fun n ↦ inferInstance
  let : ∀ n : ℕ, PreservesFiniteColimits (systemEvaluation B n) := fun n ↦ inferInstance
  let : ∀ n : ℕ, PreservesFiniteLimits (restriction A B α n) := fun n ↦ inferInstance
  let : ∀ n : ℕ, PreservesFiniteColimits (restriction A B α n) := fun n ↦ inferInstance
  obtain ⟨G, F, hG, hF, e, π, adj, hmap, htrans, hπ, hcone, hlim, hsection,
    L, R, ε, η, dAdj, hL, hR, hε, hη, hres, hnorm⟩ := derivedAdjunction A B α
  refine ⟨G, F, hG, hF, e, π, adj, ?_⟩
  refine ⟨hmap, htrans, hπ, hcone, hlim, hsection, ?_⟩
  refine ⟨L, R, ε, η, dAdj, ?_⟩
  refine ⟨hL, hR, hε, hη, hres, hnorm, ?_⟩
  obtain ⟨U0, hUadd, hUlim, hUcolim, uObj, uEval, πOrd, fLim,
    hUmap, hUtrans, huEval, hπOrd, hfLim, ho, hacyclic⟩ :=
    ordinaryRestrictionData A B α F π hπ hcone hlim
  refine ⟨U0, inferInstance, inferInstance, inferInstance, uObj, ?_⟩
  obtain ⟨RL, etaLim, hRL, hηLim, hresLim, _⟩ :=
    CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients
      J ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)
      (fun U a b ↦ @mul_comm (A.obj.obj U) inferInstance a b)
  refine ⟨uEval, πOrd, fLim, RL, etaLim, ?_⟩
  choose levelAdj hlevel using fun n : ℕ ↦ ordinaryLevel A B α G e hmap n
  let P : CochainComplex (Modules A) ℤ → Prop := fun Q ↦
    Q.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, (Q.X i).IsFlatOnSite
  have hflatRes (K : CochainComplex (Modules A) ℤ) :
      ∃ (Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ K), P Q ∧ QuasiIso q :=
    by
      obtain ⟨Q, q, hQ, hflat, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) K
      refine ⟨Q, q, ⟨hQ, fun i ↦ ?_⟩, hq⟩
      exact (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso A (Q.X i)).symm (hflat i)
  have hcomp (Q) (hQ : P Q) : IsIso (ε.app Q) := hε Q hQ.1 hQ.2
  have ha (n : ℕ) := ordinaryProjectionOnComplexes G F (systemEvaluation B n)
    (restriction A B α n) adj (levelAdj n) (πOrd n) (by
      intro N
      rw [hπOrd]
      exact ordinaryProjection A B α G F e π adj hsection n (levelAdj n) (hlevel n) N)
  let : IsGrothendieckAbelian.{w} (StrictRingSystem B) :=
    strictRingSystem_isGrothendieckAbelian B
  let : Abelian.HasKInjectiveResolutions (StrictRingSystem B) := inferInstance
  let : ∀ n : ℕ, (systemEvaluation B n).Additive := fun n ↦ inferInstance
  let : ∀ n : ℕ, (restriction A B α n).Additive := fun n ↦ inferInstance
  let : ∀ n : ℕ,
      (((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℕ, PreservesFiniteLimits
      ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)) := fun n ↦ inferInstance
  let : ∀ n : ℕ, PreservesFiniteColimits
      ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)) := fun n ↦ inferInstance
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨piLim, xi, c, derivedLevelAdj, hdata⟩ := derivedLimitAdjunctionAssembly
      (D := Modules A) (E := StrictRingSystem B) (T := ℕᵒᵖ ⥤ Modules A)
      (K := systemLevel B) G F adj U0 (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)
      (fun n ↦ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))
      (systemEvaluation B) (restriction A B α) uEval πOrd fLim (fun n ↦ lim.π (op n)) ho
      L R ε η dAdj hL hR hnorm RL etaLim hRL hηLim hresLim hacyclic
      levelAdj ha P hflatRes hcomp
      (fun levelAdj ↦ ∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V)
                (by
                  set_option backward.isDefEq.respectTransparency.types false in
                    exact inferInstance) b
                (h.val.app V x)) hlevel
  exact ⟨piLim, xi, c, levelAdj, derivedLevelAdj,
    @hUmap, @hUtrans, huEval, hπOrd, hfLim, hRL, hηLim, hdata⟩

end SheafOfModules.SequenceProjection
