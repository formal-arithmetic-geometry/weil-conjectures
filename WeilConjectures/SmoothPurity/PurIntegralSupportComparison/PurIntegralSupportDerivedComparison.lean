/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-! # Canonical compact-support comparison in strict quotient coordinates

Source: current blueprint sk-prop-sp-integral-adjunction, outer Hom comparisons;
Zheng Constructions 4.1 and 5.15, Lemma 4.10; the universal-unit normalization of
integralExceptionalComparison_characterization
(blueprint: def-pur-integral-support-coordinate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
attribute [local instance] BrownTowerComparison.ProCompact.openAdditive
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

private theorem kan_post_equivalence (L : A ⥤ B) (F : A ⥤ H)
    (R : B ⥤ H) (η : F ⟶ L ⋙ R) [R.IsLeftKanExtension η]
    (G : H ⥤ E) [G.IsEquivalence] :
    (R ⋙ G).IsLeftKanExtension
      (Functor.whiskerRight η G ≫ (Functor.associator _ _ _).hom) := by
  have : (Functor.LeftExtension.postcompose₂ L F G).IsEquivalence :=
    inferInstanceAs (StructuredArrow.map₂
      (R := (Functor.whiskeringLeft A B H).obj L) (L := F)
      (R' := (Functor.whiskeringLeft A B E).obj L) (L' := F ⋙ G)
      (F := (Functor.whiskeringRight B H E).obj G)
      (G := (Functor.whiskeringRight A H E).obj G)
      (𝟙 _) (NatIso.ofComponents (fun _ ↦ Functor.associator _ _ _)
        (by cat_disch)).hom).IsEquivalence
  exact ⟨⟨IsInitial.ofIso (IsInitial.isInitialObj
    (Functor.LeftExtension.postcompose₂ L F G) _ (R.isUniversalOfIsLeftKanExtension η))
    (Functor.LeftExtension.postcompose₂ObjMkIso G η)⟩⟩

private theorem kan_of_fullyFaithful (L : A ⥤ B) (F : B ⥤ H)
    (ff : ((Functor.whiskeringLeft A B H).obj L).FullyFaithful) :
    F.IsLeftKanExtension (𝟙 (L ⋙ F)) := by
  refine ⟨⟨IsInitial.ofUniqueHom (fun T ↦
    StructuredArrow.homMk (ff.preimage T.hom) (by simpa using ff.map_preimage T.hom)) ?_⟩⟩
  intro T m
  apply StructuredArrow.hom_ext
  apply ff.map_injective
  change Functor.whiskerLeft L m.right = Functor.whiskerLeft L (ff.preimage T.hom)
  have hm : Functor.whiskerLeft L m.right = T.hom := by simpa using m.w
  exact hm.trans (ff.map_preimage T.hom).symm

private theorem kan_precompose (L : A ⥤ B) (K : B ⥤ E) (F : B ⥤ H)
    (R : E ⥤ H) (η : F ⟶ K ⋙ R) [R.IsLeftKanExtension η]
    (ff : ((Functor.whiskeringLeft A B H).obj L).FullyFaithful) :
    R.IsLeftKanExtension
      (Functor.whiskerLeft L η ≫ (Functor.associator _ _ _).inv) := by
  have := kan_of_fullyFaithful L F ff
  exact (Functor.isLeftKanExtension_iff_postcompose
    (𝟙 (L ⋙ F)) (L ⋙ K) (Iso.refl _) η _ (by simp)).1 inferInstance

private theorem cochain_rightUnit_kan
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.rightDerivedFunctor.IsLeftKanExtension (rightUnit F) := by
  let L := HomotopyCategory.quotient A (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hη := Functor.IsRightDerivedFunctor.isLeftKanExtension
    F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (.up ℤ))
  let ff := Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj L)
  have hk := kan_precompose L DerivedCategory.Qh H F.rightDerivedFunctor
    F.rightDerivedFunctorUnit ff
  let s : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ L ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm
        DerivedCategory.Qh ≪≫ Functor.associator _ _ _
  let k := DerivedCategory.quotientCompQhIso A
  let η := Functor.whiskerLeft L F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv
  have hk' : F.rightDerivedFunctor.IsLeftKanExtension
      (η ≫ Functor.whiskerRight k.hom F.rightDerivedFunctor) := by
    let i : (L ⋙ DerivedCategory.Qh) ⋙ 𝟭 (DerivedCategory A) ≅ DerivedCategory.Q :=
      Functor.rightUnitor _ ≪≫ k
    have hh := (Functor.isLeftKanExtension_iff_postcomp₁
      (𝟭 (DerivedCategory A)) i
      (η ≫ Functor.whiskerRight k.hom F.rightDerivedFunctor))
    apply hh.2
    apply (Functor.isLeftKanExtension_iff_of_iso (Functor.leftUnitor F.rightDerivedFunctor).symm η
      ((η ≫ Functor.whiskerRight k.hom F.rightDerivedFunctor) ≫
        Functor.whiskerRight i.inv F.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom) ?_).1 hk
    ext P
    simp [η, i, k, ← Functor.map_comp]
    erw [Category.comp_id]
  apply (Functor.isLeftKanExtension_iff_of_iso₂
    (η ≫ Functor.whiskerRight k.hom F.rightDerivedFunctor) (rightUnit F)
    s.symm (Iso.refl _) ?_).1 hk'
  ext P
  simp [s, η, k, rightUnit, rightUnitApp, Functor.mapHomotopyCategoryFactors]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, Category.id_comp]

private theorem kan_square
    {A A' B B' H H' : Type*}
    [Category A] [Category A'] [Category B] [Category B'] [Category H] [Category H']
    (Q : A ⥤ B) (Q' : A' ⥤ B') (C : A ⥤ A') [C.IsEquivalence]
    (CD : B ⥤ B') [CD.IsEquivalence] (E : H ⥤ H') [E.IsEquivalence]
    (F : A ⥤ H) (G : A' ⥤ H') (RF : B ⥤ H) (RG : B' ⥤ H')
    (ηF : F ⟶ Q ⋙ RF) (ηG : G ⟶ Q' ⋙ RG)
    [RF.IsLeftKanExtension ηF] [RG.IsLeftKanExtension ηG]
    (k : Q ⋙ CD ≅ C ⋙ Q') (e : C ⋙ G ≅ F ⋙ E) :
    ∃! δ : CD ⋙ RG ≅ RF ⋙ E, ∀ P,
      ηG.app (C.obj P) ≫ RG.map (k.inv.app P) ≫ δ.hom.app (Q.obj P) =
        e.hom.app P ≫ E.map (ηF.app P) := by
  let α : C ⋙ G ⟶ Q ⋙ (CD ⋙ RG) :=
    Functor.whiskerLeft C ηG ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight k.inv RG ≫ (Functor.associator _ _ _).hom
  let β : C ⋙ G ⟶ Q ⋙ (RF ⋙ E) := e.hom ≫
    Functor.whiskerRight ηF E ≫ (Functor.associator _ _ _).hom
  have hh := kan_precompose C Q' G RG ηG
    (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft A A' H').obj C))
  have hα : (CD ⋙ RG).IsLeftKanExtension α :=
    by
      simpa only [α, Category.assoc] using
        (Functor.isLeftKanExtension_iff_postcomp₁ CD k
          (Functor.whiskerLeft C ηG ≫ (Functor.associator _ _ _).inv)).1 hh
  have hp := kan_post_equivalence Q F RF ηF E
  have hβ : (RF ⋙ E).IsLeftKanExtension β := by
    apply (Functor.isLeftKanExtension_iff_of_iso₂
      (Functor.whiskerRight ηF E ≫ (Functor.associator _ _ _).hom)
      β e.symm (Iso.refl _) ?_).1 hp
    ext P
    simp [β]
  let δ := Functor.leftKanExtensionUnique (CD ⋙ RG) α (RF ⋙ E) β
  refine ⟨δ, ?_, ?_⟩
  · intro P
    have hd := Functor.descOfIsLeftKanExtension_fac_app (CD ⋙ RG) α (RF ⋙ E) β P
    simpa [δ, Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso,
      α, β] using hd
  · intro δ' hδ'
    apply Iso.ext
    apply Functor.hom_ext_of_isLeftKanExtension (CD ⋙ RG) α
    ext P
    change α.app P ≫ δ'.hom.app (Q.obj P) = α.app P ≫ δ.hom.app (Q.obj P)
    calc
      _ = β.app P := by simpa [α, β] using hδ' P
      _ = _ := by
        simp [δ, Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso]

private theorem localization_square :
    ∃! δ : FD ⋙ EB ≅ EA ⋙ FlD, ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        FlD.map (φA.hom.app P) ≫
        φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫
        φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
  let ψF : DerivedCategory.Q ⋙ (FD ⋙ EB) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF EB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φB
  let ψl : DerivedCategory.Q ⋙ (EA ⋙ FlD) ≅
      eA.mapHomologicalComplex (.up ℤ) ⋙
        Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φA FlD ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φl
  let γ := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  let τ := ψF ≪≫ isoWhiskerRight γ DerivedCategory.Q ≪≫ ψl.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)
  let δ := ff.preimageIso τ
  have hδ : ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫ FlD.map (φA.hom.app P) ≫
        φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫
        φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
    intro P
    have hd : δ.hom.app (DerivedCategory.Q.obj P) = τ.hom.app P := by
      exact congr_app (ff.map_preimage τ.hom) P
    rw [hd]
    dsimp only [τ, ψF, ψl, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc,
      ← FlD.map_comp_assoc, Iso.inv_hom_id_app]
    erw [FlD.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
    rfl
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro P
  apply (cancel_mono (FlD.map (φA.hom.app P) ≫
    φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P))).1
  exact (hδ' P).trans (hδ P).symm

/-- A fixed ordinary normalized comparison admits a unique derived extension.
Source: Stacks 05RU, 0D6E; Zheng Lemma 4.10; blueprint integral Hom display
(blueprint: lem-pur-integral-support-derived-comparison).

Proof: apply the fixed ordinary openExtension and inverse properPush termwise to
complexes. Naturality makes these chain maps and fixes their component equations.
For open extension, combine the two exact localization factorizations with the
termwise isomorphism. The fully faithful precomposition with the localization Q
lifts this to derivedOpen and gives exactly derivedOpen_factors; it also gives
uniqueness. The coordinate equivalences are exact and preserve K-injectives, so the
proper right-derived pairs transported through them are universal right-derived
pairs for the same ordinary proper direct image. Their unique comparison is an
isomorphism. The right-derived factorization equation, with properPush inverted,
is precisely derivedProper_unit. Uniqueness of right-derived transformations gives
uniqueness of derivedProper. Componentwise extensionality fixes the two chain-map
fields; proof irrelevance then identifies the entire Derived record. This argument
assumes the Ordinary record as a parameter and constructs no ordinary comparison. -/
theorem derived_existsUnique (B : Ordinary l E S G H D) :
    ∃! R : Derived l E S G H D B, True := by
  let CX := integralExceptionalCoordinates l E X
  let CZ := integralExceptionalCoordinates l E c.Z
  let CY := integralExceptionalCoordinates l E Y
  let j := SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E) c.i
  let g := SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) c.g
  have : CX.Additive := integralExceptionalCoordinates_additive l E X
  have : CZ.Additive := integralExceptionalCoordinates_additive l E c.Z
  have : CY.Additive := integralExceptionalCoordinates_additive l E Y
  have : CZ.IsEquivalence := integralExceptionalCoordinates_equivalence l E c.Z
  have : CY.IsEquivalence := integralExceptionalCoordinates_equivalence l E Y
  have : j.Additive := SemilinearProperOpen.extension_additive
    (quotientRings l E) (quotientMaps l E) c.i
  have : g.Additive := SemilinearProperOpen.push_additive
    (quotientRings l E) (quotientMaps l E) c.g
  let bj := Functor.mapHomologicalComplexCompIso B.openExtension (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (j ⋙ CZ)) (.up ℤ)).symm
  let bg := Functor.mapHomologicalComplexCompIso B.properPush.symm (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (g ⋙ CY)) (.up ℤ)).symm
  obtain ⟨q, hq, uq⟩ := localization_square CX j D.compact.openExtension CZ
    CX.mapDerivedCategory j.mapDerivedCategory D.compact.derivedOpen CZ.mapDerivedCategory
    CX.mapDerivedCategoryFactors j.mapDerivedCategoryFactors D.compact.openFactors
    CZ.mapDerivedCategoryFactors B.openExtension
  have : (CZ.mapHomologicalComplex (.up ℤ)).IsEquivalence :=
    inferInstanceAs (CZ.asEquivalence.mapHomologicalComplex (.up ℤ)).functor.IsEquivalence
  have := D.compact.properDerived.isRightDerived
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension
    D.compact.properDerived.direct D.compact.properDerived.directUnit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  have := cochain_rightUnit_kan g
  let ep := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight bg DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (g.mapHomologicalComplex (.up ℤ))
      CY.mapDerivedCategoryFactors.symm ≪≫ (Functor.associator _ _ _).symm
  have ep_app (P : CochainComplex (coefficientSequenceModules l E c.Z) ℤ) :
      ep.hom.app P = DerivedCategory.Q.map (bg.hom.app P) ≫
        CY.mapDerivedCategoryFactors.inv.app ((g.mapHomologicalComplex (.up ℤ)).obj P) := by
    dsimp only [ep, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨p, hp, up⟩ := kan_square DerivedCategory.Q DerivedCategory.Q
    (CZ.mapHomologicalComplex (.up ℤ)) CZ.mapDerivedCategory CY.mapDerivedCategory
    (g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (D.compact.properImage.rightSystem.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    g.rightDerivedFunctor D.compact.properDerived.direct
    (rightUnit g) D.compact.properDerived.directUnit CZ.mapDerivedCategoryFactors ep
  let R : Derived l E S G H D B := {
    openComplex := fun P ↦ bj.hom.app P
    openComplex_component := fun P i ↦ by
      change B.openExtension.hom.app (P.X i) ≫ 𝟙 _ = _
      exact Category.comp_id _
    properComplex := fun P ↦ bg.hom.app P
    properComplex_component := fun P i ↦ by
      change B.properPush.inv.app (P.X i) ≫ 𝟙 _ = _
      exact Category.comp_id _
    derivedOpen := q
    derivedOpen_factors := hq
    derivedProper := p
    derivedProper_unit := fun P ↦ by
      have h := hp P
      rw [ep_app] at h
      dsimp only [CZ, CY, g, rightUnit, coordinates, Functor.asEquivalence,
        SemilinearProperOpen.R] at h ⊢
      simpa only [Category.assoc] using h }
  refine ⟨R, trivial, ?_⟩
  intro R' _
  have ho : R'.openComplex = R.openComplex := by
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    exact (R'.openComplex_component P i).trans (R.openComplex_component P i).symm
  have hg : R'.properComplex = R.properComplex := by
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    exact (R'.properComplex_component P i).trans (R.properComplex_component P i).symm
  have hq' : R'.derivedOpen = q := by
    apply uq
    intro P
    have h := R'.derivedOpen_factors P
    rw [ho] at h
    exact h
  have hp' : R'.derivedProper = p := by
    apply up
    intro P
    have h := R'.derivedProper_unit P
    rw [hg] at h
    rw [ep_app]
    dsimp only [R, CZ, CY, g, rightUnit, coordinates, Functor.asEquivalence,
      SemilinearProperOpen.R] at h ⊢
    simpa only [Category.assoc] using h
  have hq'' : R'.derivedOpen = R.derivedOpen := hq'
  have hp'' : R'.derivedProper = R.derivedProper := hp'
  cases R'
  dsimp only [R] at ho hg hq'' hp'' ⊢
  cases ho
  cases hg
  cases hq''
  cases hp''
  rfl

end WeilConjectures.PurIntegralSupportComparison
