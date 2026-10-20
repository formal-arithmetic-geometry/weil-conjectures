/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Derived adjunctions computed by a left resolving class

Source: Stacks Project, Derived Categories, Tags 06XN, 05SE, 09T5, 0FND.
(blueprint: lem-sfb-resolving-derived-adjunction-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem leftDerivedOnComplexes
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (G : A ⥤ B) [G.Additive]
    {T : Type*} [Category T] (H : DerivedCategory B ⥤ T)
    (L : DerivedCategory A ⥤ T)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ H)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    ∃ εc : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ H,
      L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ P, εc.app P = ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q ⋙ L ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ H :=
    { app := fun P ↦ ε.app (π.obj P)
      naturality := fun _ _ f ↦ ε.naturality (π.map f) }
  refine ⟨εc, ⟨⟨⟨?_⟩⟩⟩, fun _ ↦ rfl⟩
  let lift (Z : DerivedCategory A ⥤ T)
      (τ : DerivedCategory.Q ⋙ Z ⟶
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ H) :
      DerivedCategory.Qh ⋙ Z ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ H :=
    { app := fun X ↦ τ.app X.as
      naturality := by
        intro X Y f
        obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
        obtain ⟨f, rfl⟩ := π.map_surjective f
        exact τ.naturality f }
  refine IsTerminal.ofUniqueHom (fun Z ↦ CostructuredArrow.homMk
    (L.leftDerivedLift ε (HomotopyCategory.quasiIso A (.up ℤ)) Z.left
      (lift Z.left Z.hom)) (by
        apply NatTrans.ext
        funext P
        exact L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
          Z.left (lift Z.left Z.hom) (π.obj P))) ?_
  intro Z m
  apply CostructuredArrow.hom_ext
  apply L.leftDerived_ext ε (HomotopyCategory.quasiIso A (.up ℤ))
  apply NatTrans.ext
  funext X
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hm := NatTrans.congr_app m.w P
  have hm' : m.left.app (DerivedCategory.Q.obj P) ≫ ε.app (π.obj P) =
      Z.hom.app P := by simpa using hm
  exact hm'.trans
    (L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
      Z.left (lift Z.left Z.hom) (π.obj P)).symm


/-- A resolving left derived functor and a K-injective right derived functor have the
canonical derived adjunction, with its Hom bijection normalized on every chain map.
Source: Stacks Project, Tags 06XN, 05SE and 09T5, applied in the proof of Tag 07A6.
(blueprint: lem-sfb-resolving-derived-adjunction-normalization).

Proof: resolving-class essential constancy makes the left-derived Kan extension
absolute, so postcomposition by the right derived functor preserves it. The
K-injective derivability structure shows that postcomposition of the right-derived
comparison by the left derived functor is again right derived. Transfer the left
universal property across the full, object-surjective homotopy quotient and apply
the derived-adjunction theorem on complexes. Its unit factorization and naturality
of the right-derived comparison give the displayed Hom formula. -/
theorem derivedAdjunctionOfResolvingClass
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions B]
    (G : A ⥤ B) (F : B ⥤ A) [G.Additive] [F.Additive] (adj : G ⊣ F)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}).map s))
    (L : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (εh : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso A (.up ℤ)))
    (RF : DerivedCategory.{w} B ⥤ DerivedCategory.{w} A)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))) :
    ∃ d : L ⊣ RF,
      ∀ (M : CochainComplex A ℤ) (I : CochainComplex B ℤ)
        (f : (G.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (εh.app ((HomotopyCategory.quotient A (.up ℤ)).obj M) ≫
              DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            η.app I := by
  classical
  let GF := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  let := hL
  let := hRF
  obtain ⟨ε, hε, hεapp⟩ := leftDerivedOnComplexes G (𝟭 (DerivedCategory.{w} B)) L εh
  let := hε
  have hRFL : (RF ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight η L ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
    have hd : (CochainComplex.KInjectives.localizerMorphism B).Derives
        (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⋙ L) := by
      intro I I' f hf
      have : IsIso (DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map f.hom)) := (CategoryTheory.derives F) f hf
      exact L.map_isIso (DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) :=
      (CategoryTheory.derives F).isIso_of_isRightDerivedFunctor η I
    change IsIso (L.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let := hRFL
  let : (HomotopyCategory.quasiIso A (.up ℤ)).HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated A).2.2.2.2.1
  have hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ GF) Y := by
    intro X
    obtain ⟨Y, _, hy, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso A (.up ℤ)) GF P hres hinv X
    exact ⟨Y, hy⟩
  have : RF.PreservesRightKanExtension GF DerivedCategory.Qh :=
    _root_.pro_absolute (HomotopyCategory.quasiIso A (.up ℤ))
      DerivedCategory.Qh GF RF hc
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension L εh
    (HomotopyCategory.quasiIso A (.up ℤ))
  have hLRFh : (L ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh RF)
      (HomotopyCategory.quasiIso A (.up ℤ)) := ⟨inferInstance⟩
  let := hLRFh
  obtain ⟨δ, hδ, hδapp⟩ := leftDerivedOnComplexes G RF (L ⋙ RF)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh RF)
  have hδeq : δ = (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε RF := by
    apply NatTrans.ext
    funext X
    simp only [hδapp, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, hεapp]
  rw [hδeq] at hδ
  let := hδ
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived (L₂ := DerivedCategory.Q.{w}) (HomologicalComplex.quasiIso A (.up ℤ))
    (HomologicalComplex.quasiIso B (.up ℤ)) ε η
  refine ⟨d, ?_⟩
  intro M I f
  rw [← hεapp M]
  change d.unit.app _ ≫ RF.map (ε.app M ≫ DerivedCategory.Q.map f) = _
  rw [RF.map_comp, ← Category.assoc]
  have hunit := ac.derivedη_fac_app (HomologicalComplex.quasiIso A (.up ℤ)) ε η M
  change d.unit.app _ ≫ RF.map (ε.app M) = _ at hunit
  have hn := η.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hunit, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

end CategoryTheory
