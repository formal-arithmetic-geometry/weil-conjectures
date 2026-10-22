/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RingedDerivedSliceData
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Sheaf.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Derived slice proof obligations

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-slice-derived-image-exists).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

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

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Derived comparisons use both complex and homotopy localization presentations.
/-- The canonical module adjunction has normalized total derived functors.
Source: Stacks Tags 06YY, 070K and 09T5
(blueprint: lem-weil-pbc-ringed-slice-derived-image-exists).
Proof:
1. The continuous ringed-topos presentation identifies its module direct image
with the canonical site direct image F. Its K-flat pullback theorem supplies an
additive left adjoint preserving quasi-isomorphisms between flat-term K-flat
complexes. Uniqueness of left adjoints transfers this property to the canonical
pullback G.
2. Flat-term K-flat resolutions define a resolving class in the homotopy category.
The resolving-class theorem constructs L with its left-derived comparison epsilon,
invertible on that class. K-injective derivability constructs RF with its universal
right-derived comparison eta. Fullness and surjectivity of the homotopy quotient
transfer the left-derived universal property to the category of complexes.
3. The resolving-class denominator diagrams are essentially constant pro-diagrams.
Their absolute limit property implies that postcomposition by RF preserves the
left-derived universal property of L. K-injective derivability similarly shows
that postcomposition of RF by L remains right derived: its comparison is invertible
on K-injectives. Mathlib's derived-adjunction construction therefore applies to
the original complex adjunction and these universal transformations.
4. The derived unit factorization and naturality of eta prove the displayed Hom
normalization for every chain map. The resolving-class comparison is invertible
on every flat-term K-flat complex, as required. -/
theorem ringedSliceDerivedImage_exists
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] :
    ∃ e : RingedSliceDerivedImage.{u, w} u a,
      ∀ P : CochainComplex (SheafOfModules.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ,
        P.IsAcyclicTensorKFlat →
          (∀ n : ℤ, letI := monoidalCategory R
            exactFunctor _ _ (MonoidalCategory.tensorRight (P.X n))) →
          IsIso (e.epsilon.app P) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
  let B := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  let G := ringedSliceModulePullback u a
  let F := ringedSliceModulePushforward u a
  let πA := HomotopyCategory.quotient A (.up ℤ)
  let πB := HomotopyCategory.quotient B (.up ℤ)
  let GF := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  have hpres : ∀ (P Q : CochainComplex A ℤ) (s : P ⟶ Q),
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
      Q.IsAcyclicTensorKFlat → (∀ n : ℤ, (Q.X n).IsFlat) → QuasiIso s →
        QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map s) := by
    obtain ⟨f, hf⟩ := continuousRingedToposModuleDirectImage_exists u
      (u.sheafPullback (Type u) K J) (u.sheafAdjunctionContinuous (Type u) K J) S R a
    obtain ⟨G', hG', adj', _, hinv⟩ := f.exists_kFlatPullback J K S R
    have adj'' : G' ⊣ F := by
      change G' ⊣ ringedSliceModulePushforward u a
      simpa only [hf, ringedSliceModulePushforward, ringedSiteModuleMap] using adj'
    let c := NatIso.mapHomologicalComplex
      (adj''.leftAdjointUniq (ringedSliceModuleAdjunction u a)) (.up ℤ)
    intro P Q s hP hPf hQ hQf hs
    have h := hinv P Q s hP hPf hQ hQf hs
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app P) (c.app Q) (c.hom.naturality s).symm)).1 h
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
    Functor.leftDerived_from_resolvingClass A (DerivedCategory.{w} B) GF P hres hinv
  let := hL
  obtain ⟨ε, hε, hεapp⟩ := leftDerivedOnComplexes G (𝟭 (DerivedCategory.{w} B)) L εh
  let := hε
  let := (grothendieckAbelian_and_functorial_kInjective_resolutions J S).1
  obtain ⟨RF, η, hη, hηgood⟩ := CategoryTheory.exists_derived F
  let := hη
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
  let adj := (ringedSliceModuleAdjunction u a).mapHomologicalComplex (.up ℤ)
  let d := adj.derived (L₂ := DerivedCategory.Q.{w}) (HomologicalComplex.quasiIso A (.up ℤ))
    (HomologicalComplex.quasiIso B (.up ℤ)) ε η
  refine ⟨⟨L, RF, ε, η, hε, hη, d, ?_⟩, ?_⟩
  · intro M I f
    change d.unit.app _ ≫ RF.map (ε.app M ≫ DerivedCategory.Q.map f) = _
    rw [RF.map_comp, ← Category.assoc]
    have hunit := adj.derivedη_fac_app (HomologicalComplex.quasiIso A (.up ℤ)) ε η M
    change d.unit.app _ ≫ RF.map (ε.app M) = _ at hunit
    have hn := η.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [hunit, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
    rfl
  · intro M hM hf
    change IsIso (ε.app M)
    rw [hεapp]
    exact hεh (πA.obj M) ⟨M, rfl, hM, hf⟩

end SheafOfModules
