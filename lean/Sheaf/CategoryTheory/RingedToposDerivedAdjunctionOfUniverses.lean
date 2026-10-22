/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X5
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.CategoryTheory.RingedToposKFlatPullback
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # A derived left adjoint with independent localization universes

Source: Stacks Project, Tags 06XN and 09T5.
(blueprint: lem-weil-pbc-ringed-derived-adjunction-independent-universes).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem leftDerivedOnComplexes
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{wY} A] [HasDerivedCategory.{wX} B]
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

private theorem quasiIso_twoOutOfThree
    (A : Type*) [Category A] [Abelian A] :
    (HomotopyCategory.quasiIso A (.up ℤ)).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    intro n
    let H := HomotopyCategory.homologyFunctor A (.up ℤ) n
    have : IsIso (H.map g) := hg n
    have : IsIso (H.map f ≫ H.map g) := by
      simpa only [Functor.map_comp] using hfg n
    exact IsIso.of_isIso_comp_right (H.map f) (H.map g)
  of_precomp f g hf hfg := by
    intro n
    let H := HomotopyCategory.homologyFunctor A (.up ℤ) n
    have : IsIso (H.map f) := hf n
    have : IsIso (H.map f ≫ H.map g) := by
      simpa only [Functor.map_comp] using hfg n
    exact IsIso.of_isIso_comp_left (H.map f) (H.map g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 200000 in
-- The proof uses both complex and homotopy localization presentations.
/-- A right derived module direct image has its K-flat-derived left adjoint, without
identifying the universes of the two derived categories. The same construction
records its ordinary module left adjoint and the homotopy left-derived comparison,
including invertibility on flat-term K-flat representatives.

Source: Stacks Project, Tags 06XN (resolving class) and 09T5 (derived adjunction).
(blueprint: lem-weil-pbc-ringed-derived-adjunction-independent-universes).

Proof: the module inverse-image adjunction preserves quasi-isomorphisms between
flat-term K-flat complexes. Such complexes resolve every complex, so the resolving
class constructs a left derived functor. Its denominator pro-diagrams are essentially
constant, hence every functor preserves the resulting right Kan extension. On the
other side, the given direct-image comparison computes on K-injectives, and remains
a derived comparison after any postcomposition. These two absolute derived properties
let the ordinary complex adjunction descend by the derived-adjunction theorem. -/
theorem RingedToposMorphism.exists_derivedLeftAdjoint
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I)) :
    ∃ L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX,
      Nonempty (L ⊣ Rf) ∧
      ∃ G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
          ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX),
        Nonempty (G ⊣ f.modules) ∧ ∃ hG : G.Additive,
        letI := hG
        ∃ ε : DerivedCategory.Qh.{wY} ⋙ L ⟶
            G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{wX},
          L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso
            (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
            (.up ℤ)) ∧
          ∀ P : CochainComplex (ringedSiteModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ℤ,
            P.IsAcyclicTensorKFlat →
            (∀ n : ℤ, (P.X n).IsFlat) →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  classical
  let : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)
  let B := SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
  let : Category A := inferInstance
  let : Category B := inferInstance
  let : Abelian A := inferInstance
  let : Abelian B := inferInstance
  let : HasDerivedCategory.{wY} A := inferInstance
  let : HasDerivedCategory.{wX} B := inferInstance
  obtain ⟨G, hG, adj, _, hpres⟩ := f.exists_kFlatPullback K J RX RY
  let := hG
  let πA := HomotopyCategory.quotient A (.up ℤ)
  let GF := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{wX}
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ M : CochainComplex A ℤ, πA.obj M = X ∧
      M.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (M.X n).IsFlat}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨M, s, hM, hf, hs, _⟩ := CochainComplex.exists_isKFlatResolution X
    exact ⟨πA.obj M, πA.map s, ⟨M, rfl, hM, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (GF.map s) := by
    intro X Y s hX hY hs
    obtain ⟨X, rfl, hX, hfX⟩ := hX
    obtain ⟨Y, rfl, hY, hfY⟩ := hY
    obtain ⟨s, rfl⟩ := πA.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres X Y s hX hfX hY hfY hq
    change IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (πA.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, L, εh, hL, _, hεh⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory.{wX} B) GF P hres hinv
  let := hL
  obtain ⟨ε, hε, hεapp⟩ := leftDerivedOnComplexes G (𝟭 (DerivedCategory.{wX} B)) L εh
  let := hε
  let := hRf
  let : IsGrothendieckAbelian.{u} B := SheafOfModules.isGrothendieckAbelian _
  have hRFL : (Rf ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight ρ L ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
    have hd : (CochainComplex.KInjectives.localizerMorphism B).Derives
        (f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{wY} ⋙ L) := by
      intro I I' g hg
      have : IsIso (DerivedCategory.Q.map
          ((f.modules.mapHomologicalComplex (.up ℤ)).map g.hom)) :=
        (CategoryTheory.derives f.modules) g hg
      exact L.map_isIso (DerivedCategory.Q.map
        ((f.modules.mapHomologicalComplex (.up ℤ)).map g.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (ρ.app I.obj) := hCompute I.obj I.property
    change IsIso (L.map (ρ.app I.obj) ≫ 𝟙 _)
    infer_instance
  let := hRFL
  let := quasiIso_twoOutOfThree A
  have hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ GF) Y := by
    intro X
    obtain ⟨Y, _, hy, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso A (.up ℤ)) GF P hres hinv X
    exact ⟨Y, hy⟩
  have : Rf.PreservesRightKanExtension GF (DerivedCategory.Qh.{wY} (C := A)) :=
    _root_.pro_absolute (HomotopyCategory.quasiIso A (.up ℤ))
      (DerivedCategory.Qh.{wY} (C := A)) GF Rf hc
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension L εh
    (HomotopyCategory.quasiIso A (.up ℤ))
  have hLRFh : (L ⋙ Rf).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh Rf)
      (HomotopyCategory.quasiIso A (.up ℤ)) := ⟨inferInstance⟩
  let := hLRFh
  obtain ⟨δ, hδ, hδapp⟩ := leftDerivedOnComplexes G Rf (L ⋙ Rf)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh Rf)
  have hδeq : δ = (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε Rf := by
    apply NatTrans.ext
    funext X
    simp only [hδapp, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, hεapp]
  rw [hδeq] at hδ
  let := hδ
  refine ⟨L, ⟨(adj.mapHomologicalComplex (.up ℤ)).derived
    (L₁ := DerivedCategory.Q.{wY} (C := A))
    (L₂ := DerivedCategory.Q.{wX} (C := B)) (HomologicalComplex.quasiIso A (.up ℤ))
      (HomologicalComplex.quasiIso B (.up ℤ)) ε ρ⟩, G, ⟨adj⟩, hG, εh, hL, ?_⟩
  intro P hk hf
  exact hεh (πA.obj P) ⟨P, rfl, hk, hf⟩

end CategoryTheory
