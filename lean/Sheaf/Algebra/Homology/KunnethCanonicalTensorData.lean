/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.DerivedCanonicalFiltration
import Sheaf.Algebra.Homology.FilteredTensorLocalization
import Mathlib.Tactic.ClearExclamation

/-! # Normalized data for canonical convolution

Source: Stacks Project, Tags 0H7X--0H7Z.
(blueprint: lem-kun-canonical-tensor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CategoryTheory.Functor
open scoped ZeroObject
namespace DerivedCategory
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

set_option genInjectivity false in
/-- The normalized canonical lift and convolution, including finite-support grading.
Source: Stacks Project, Tags 0H7X--0H7Z (blueprint: lem-kun-canonical-tensor-data). -/
structure CanonicalTensorLocalizationData where
  T : Bounded (ModuleCat.{u} R) ⥤ finiteFilteredModuleDerivedCategory R
  omega : finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R)
  gr : ℤ → finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R)
  eTomega : T ⋙ omega ≅ Bounded.ι
  eTgr : ∀ i : ℤ, T ⋙ gr i ≅ Bounded.ι ⋙
    homologyFunctor (ModuleCat.{u} R) (-i) ⋙ singleFunctor (ModuleCat.{u} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i
  eForget : ∀ P : FiniteFilteredModuleComplex R,
    omega.obj ((finiteFilteredDerivedQuotient R).obj P) ≅ Q.obj P.obj.obj
  hForget : ∀ {P P' : FiniteFilteredModuleComplex R} (f : P ⟶ P'),
    omega.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eForget P').hom =
      (eForget P).hom ≫ Q.map f.hom.hom
  eGrade : ∀ (i : ℤ) (P : FiniteFilteredModuleComplex R),
    (gr i).obj ((finiteFilteredDerivedQuotient R).obj P) ≅
      Q.obj (P.obj.filtration.gradedPiece i)
  hGrade : ∀ (i : ℤ) {P P' : FiniteFilteredModuleComplex R} (f : P ⟶ P'),
    (gr i).map ((finiteFilteredDerivedQuotient R).map f) ≫ (eGrade i P').hom =
      (eGrade i P).hom ≫ Q.map (FilteredObject.gradedMapSteps f.hom i)
  star : finiteFilteredModuleDerivedCategory R ⥤
    finiteFilteredModuleDerivedCategory R ⥤ finiteFilteredModuleDerivedCategory R
  eta : ∀ U V, omega.obj ((star.obj U).obj V) ≅ omega.obj U ⊗ omega.obj V
  eta_naturality : ∀ {U U' V V'} (f : U ⟶ U') (g : V ⟶ V'),
    (eta U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
      omega.map ((star.map f).app V ≫ (star.obj U').map g) ≫ (eta U' V').hom
  graded : ∀ a U V (s : Finset ℤ),
    (∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U ⊗ (gr (a - i)).obj V)) →
      ((gr a).obj ((star.obj U).obj V) ≅
        (⨁ fun i : ↥s ↦ (gr i.val).obj U ⊗ (gr (a - i.val)).obj V))
  finite_support : ∀ a U V, ∃ s : Finset ℤ,
    ∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U ⊗ (gr (a - i)).obj V)
  graded_naturality : ∀ a {U U' V V'} (f : U ⟶ U') (g : V ⟶ V') (s : Finset ℤ)
    (hs : ∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U ⊗ (gr (a - i)).obj V))
    (hs' : ∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U' ⊗ (gr (a - i)).obj V')),
    (graded a U V s hs).hom ≫ biproduct.map (fun i : ↥s ↦
      (gr i.val).map f ⊗ₘ (gr (a - i.val)).map g) =
        (gr a).map ((star.map f).app V ≫ (star.obj U').map g) ≫
          (graded a U' V' s hs').hom
  graded_extension : ∀ a U V (s t : Finset ℤ) (hst : s ⊆ t)
    (hs : ∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U ⊗ (gr (a - i)).obj V))
    (ht : ∀ i : ℤ, i ∉ t → IsZero ((gr i).obj U ⊗ (gr (a - i)).obj V)),
    ∃ (inc : (⨁ fun i : ↥s ↦ (gr i.val).obj U ⊗ (gr (a - i.val)).obj V) ⟶
        ⨁ fun i : ↥t ↦ (gr i.val).obj U ⊗ (gr (a - i.val)).obj V),
      (∀ i : ↥s, biproduct.ι _ i ≫ inc = biproduct.ι
        (fun j : ↥t ↦ (gr j.val).obj U ⊗ (gr (a - j.val)).obj V) ⟨i.val, hst i.property⟩) ∧
        (graded a U V s hs).hom ≫ inc = (graded a U V t ht).hom

private theorem descend_iso (R : Type u) [CommRing R]
    {C : Type*} [Category.{w} C]
    (F G : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ F ≅ finiteFilteredDerivedQuotient R ⋙ G) :
    ∃ ebar : F ≅ G, ∀ U : CochainComplex.FiniteFilteredModuleComplex R,
      ebar.hom.app ((finiteFilteredDerivedQuotient R).obj U) = e.hom.app U := by
  let q := CochainComplex.finiteFilteredModuleHomotopyQuotient R
  let L := finiteFilteredModuleLocalizationFunctor R
  let W := CochainComplex.finiteFilteredModuleQuasiIso R
  have := Localization.full_whiskeringLeft L W C
  have := Localization.faithful_whiskeringLeft L W C
  let T := (Functor.whiskeringLeft _ _ C).obj L ⋙
    (Functor.whiskeringLeft _ _ C).obj q
  have : T.Full := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  have : T.Faithful := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  let e' : T.obj F ≅ T.obj G :=
    (Functor.associator q L F).symm ≪≫ e ≪≫ Functor.associator q L G
  refine ⟨T.preimageIso e', ?_⟩
  intro U
  have he := congrArg (fun τ ↦ τ.app U) (T.map_preimage e'.hom)
  change (T.preimage e'.hom).app ((finiteFilteredDerivedQuotient R).obj U) =
    e'.hom.app U at he
  have he' : e'.hom.app U = e.hom.app U := by
    change 𝟙 _ ≫ (e.hom.app U ≫ 𝟙 _) = e.hom.app U
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact he.trans he'

private theorem compareNormalized
    (F G : finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R))
    (A : FiniteFilteredModuleComplex R → DerivedCategory (ModuleCat.{u} R))
    (eF : ∀ P, F.obj ((finiteFilteredDerivedQuotient R).obj P) ≅ A P)
    (eG : ∀ P, G.obj ((finiteFilteredDerivedQuotient R).obj P) ≅ A P)
    (mapA : ∀ {P P' : FiniteFilteredModuleComplex R}, (P ⟶ P') → (A P ⟶ A P'))
    (hF : ∀ {P P' : FiniteFilteredModuleComplex R} (f : P ⟶ P'),
      F.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eF P').hom =
        (eF P).hom ≫ mapA f)
    (hG : ∀ {P P' : FiniteFilteredModuleComplex R} (f : P ⟶ P'),
      G.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eG P').hom =
        (eG P).hom ≫ mapA f) : Nonempty (F ≅ G) := by
  let e : finiteFilteredDerivedQuotient R ⋙ F ≅ finiteFilteredDerivedQuotient R ⋙ G :=
    NatIso.ofComponents (fun P ↦ eF P ≪≫ (eG P).symm) (by
      intro P P' f
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      apply (cancel_mono (eG P').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [Functor.comp_map]
      rw [hG, Iso.inv_hom_id_assoc]
      exact hF f)
  obtain ⟨e', _⟩ := descend_iso R F G e
  exact ⟨e'⟩

/-- Construct normalized canonical convolution data by localization descent.
Source: Stacks Project, Tags 0H7X--0H7Z (blueprint: lem-kun-canonical-tensor-data).
Proof. Take the canonical lift and localized convolution. Construct the forgetful and
graded normalization from the localization lifting isomorphisms and the quotient-to-Q
comparison. Fully faithful precomposition through the quotient and localization
compares these normalizations with the canonical lift's normalizations. Whisker these
comparisons by the lift and compose with its canonical isomorphisms. All remaining
fields are the convolution comparisons and their stated support equations. -/
theorem exists_kunnethCanonicalTensorData : Nonempty (CanonicalTensorLocalizationData R) := by
  classical
  obtain ⟨FF, pi, hF, hfinite₀, hmodel, hmap, hhomotopy, hqi, T, omega₀,
    gr₀, eOmega₀, eGr₀, eForget₀, eGrade₀, hfinite₁, rep,
    hForget₀, hGrade₀, rest⟩ := exists_derivedCanonicalFiltration R
  clear! FF
  have data := filteredTensor_localization (R := R)
  obtain ⟨E, data⟩ := data
  obtain ⟨eE, data⟩ := data
  obtain ⟨FF₂, data⟩ := data
  obtain ⟨B, data⟩ := data
  obtain ⟨hB, data⟩ := data
  obtain ⟨hconv, data⟩ := data
  obtain ⟨conv, data⟩ := data
  obtain ⟨hconv₁, data⟩ := data
  obtain ⟨hconv₂, data⟩ := data
  obtain ⟨hrep, data⟩ := data
  obtain ⟨m, data⟩ := data
  obtain ⟨hm, data⟩ := data
  obtain ⟨hid, data⟩ := data
  obtain ⟨hcomp, data⟩ := data
  obtain ⟨hmap₂, data⟩ := data
  obtain ⟨star, data⟩ := data
  obtain ⟨τ, data⟩ := data
  obtain ⟨hτ, data⟩ := data
  obtain ⟨omega, data⟩ := data
  obtain ⟨Fω, data⟩ := data
  obtain ⟨hω, data⟩ := data
  obtain ⟨hωobj, data⟩ := data
  obtain ⟨hωmap, data⟩ := data
  obtain ⟨gr, data⟩ := data
  obtain ⟨Fgr, data⟩ := data
  obtain ⟨hgr, data⟩ := data
  obtain ⟨hgro, data⟩ := data
  obtain ⟨hgrmap, data⟩ := data
  obtain ⟨⟨η, hη, _, _, _⟩, eg, hfinite, hgnat, hgext, _⟩ := data
  clear! E eE FF₂ B hB hconv conv hconv₁ hconv₂ hrep m hm hid hcomp hmap₂ τ hτ
  have := hω
  have (i : ℤ) := hgr i
  let eForget := fun P : FiniteFilteredModuleComplex R ↦
    (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) Fω omega).app
        ((finiteFilteredModuleHomotopyQuotient R).obj P) ≪≫
      eqToIso (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app P.obj.obj
  let eGrade := fun (i : ℤ) (P : FiniteFilteredModuleComplex R) ↦
    (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) (Fgr i) (gr i)).app
        ((finiteFilteredModuleHomotopyQuotient R).obj P) ≪≫
      eqToIso (hgro i ((finiteFilteredModuleHomotopyQuotient R).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app
        (P.obj.filtration.gradedPiece i)
  set_option backward.isDefEq.respectTransparency false in
  have hForget (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P') :
      omega.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eForget P').hom =
        (eForget P).hom ≫ Q.map f.hom.hom := by
    dsimp only [eForget, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
    erw [← Category.assoc, (Localization.Lifting.iso
      (finiteFilteredModuleQuasiIso R).Q (finiteFilteredModuleQuasiIso R)
      Fω omega).hom.naturality, hωmap]
    simp only [Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rfl
  set_option backward.isDefEq.respectTransparency false in
  have hGrade (i : ℤ) (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P') :
      (gr i).map ((finiteFilteredDerivedQuotient R).map f) ≫ (eGrade i P').hom =
        (eGrade i P).hom ≫ Q.map (FilteredObject.gradedMapSteps f.hom i) := by
    dsimp only [eGrade, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
    erw [← Category.assoc, (Localization.Lifting.iso
      (finiteFilteredModuleQuasiIso R).Q (finiteFilteredModuleQuasiIso R)
      (Fgr i) (gr i)).hom.naturality, hgrmap]
    simp only [Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rfl
  let eω : omega₀ ≅ omega := (compareNormalized R omega₀ omega
    (fun P ↦ Q.obj P.obj.obj) eForget₀ eForget
    (fun f ↦ Q.map f.hom.hom) (fun f ↦ hForget₀ _ _ f)
      (fun f ↦ hForget _ _ f)).some
  let egr (i : ℤ) : gr₀ i ≅ gr i := (compareNormalized R (gr₀ i) (gr i)
    (fun P ↦ Q.obj (P.obj.filtration.gradedPiece i)) (eGrade₀ i) (eGrade i)
    (fun f ↦ Q.map (FilteredObject.gradedMapSteps f.hom i))
    (fun f ↦ hGrade₀ i _ _ f) (fun f ↦ hGrade i _ _ f)).some
  let eTω : T ⋙ omega ≅ Bounded.ι :=
    (Functor.isoWhiskerLeft T eω).symm ≪≫ eOmega₀
  let eTgr (i : ℤ) := (Functor.isoWhiskerLeft T (egr i)).symm ≪≫ eGr₀ i
  exact ⟨{
    T := T
    omega := omega
    gr := gr
    eTomega := eTω
    eTgr := eTgr
    eForget := eForget
    hForget := fun {P P'} f ↦ hForget P P' f
    eGrade := eGrade
    hGrade := fun i {P P'} f ↦ hGrade i P P' f
    star := star
    eta := η
    eta_naturality := fun {U U' V V'} f g ↦ hη U U' V V' f g
    graded := eg
    finite_support := hfinite
    graded_naturality := fun a {U U' V V'} f g s hs hs' ↦
      hgnat a U U' V V' f g s hs hs'
    graded_extension := hgext }⟩

end DerivedCategory
