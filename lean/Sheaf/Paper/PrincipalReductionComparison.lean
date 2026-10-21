/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedReductionResolutionIndependence
import Sheaf.Paper.PrincipalReductionFlatComparison
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Descent of the principal-reduction comparison

The flat-resolution comparison descends by the calculus of fractions, with no choice of
unit normalization. (blueprint: lem-pod-principal-reduction-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
universe u v r wO wS wR wA
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Functor

namespace SheafOfModules.PrincipalReduction.Setup
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)
  [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

private theorem good_model (X : DerivedCategory
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))) :
    ∃ P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  let M := DerivedCategory.Q.objPreimage X
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := D.O) M
  have := hp
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso D.O (P.X i)).symm (hf i)

private theorem alpha_naturality_derived
    (P P' : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i))
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P') :
    D.alpha P hP hf ≫ (D.T ⋙ D.G').map f =
      (D.G ⋙ D.L).map f ≫ D.alpha P' hP' hf' := by
  obtain ⟨S, s, hs, g, hfac⟩ := DerivedCategory.right_fac f
  have hsq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  obtain ⟨V, q, hV, hVf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := D.O) S
  have := hs
  have := hsq
  have := hq
  have hvf (i : ℤ) : IsFlatOnSite (R := D.O) (V.X i) :=
    (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso D.O (V.X i)).symm (hVf i)
  let a := q ≫ s
  let b := q ≫ g
  have ha := D.resolution_independence.1 V P hV hP hvf hf a
  have hb := D.resolution_independence.1 V P' hV hP' hvf hf' b
  have hab : DerivedCategory.Q.map a ≫ f = DerivedCategory.Q.map b := by
    simp [a, b, hfac, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((D.G ⋙ D.L).map (DerivedCategory.Q.map a))).1
  calc
    _ = D.alpha V hV hvf ≫
        (D.T ⋙ D.G').map (DerivedCategory.Q.map a) ≫ (D.T ⋙ D.G').map f := by
      rw [← Category.assoc, ← ha, Category.assoc]
    _ = D.alpha V hV hvf ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map b) := by
      rw [← Functor.map_comp, hab]
    _ = (D.G ⋙ D.L).map (DerivedCategory.Q.map b) ≫ D.alpha P' hP' hf' := hb
    _ = _ := by rw [← Functor.map_comp_assoc, hab]

/-- Exact sections commute with derived principal reduction over a domain when t is nonzero.

Proof: choose a flat-term K-flat model for each derived object. Its alpha comparison is an
isomorphism by the regular-complex quotient argument. Any derived morphism between two
models is a roof of chain maps; resolving the roof's source by a flat-term K-flat complex
lets resolution-independence naturality apply to both legs. Cancel the invertible denominator.
Transport along the chosen models and assemble a natural isomorphism.
Source: Stacks Tags 06Y6, 06YY; original blueprint steps 8--10.
(blueprint: lem-pod-principal-reduction-comparison) -/
theorem comparison [IsDomain R] (ht : D.t ≠ 0) :
    Nonempty (D.G ⋙ D.L ≅ D.T ⋙ D.G') := by
  choose P hP hf he using D.good_model
  let e X := (he X).some
  let F := D.G ⋙ D.L
  let H := D.T ⋙ D.G'
  have (X : DerivedCategory
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))) :
      IsIso (D.alpha (P X) (hP X) (hf X)) :=
    D.alpha_isIso ht (P X) (hP X) (hf X)
  refine ⟨NatIso.ofComponents (fun X ↦
    (F.mapIso (e X)).symm ≪≫ asIso (D.alpha (P X) (hP X) (hf X)) ≪≫
      H.mapIso (e X)) ?_⟩
  intro X Y f
  have hn := D.alpha_naturality_derived (P X) (P Y) (hP X) (hP Y) (hf X) (hf Y)
    ((e X).hom ≫ f ≫ (e Y).inv)
  change F.map f ≫ (F.map (e Y).inv ≫ D.alpha (P Y) (hP Y) (hf Y) ≫
    H.map (e Y).hom) =
    (F.map (e X).inv ≫ D.alpha (P X) (hP X) (hf X) ≫ H.map (e X).hom) ≫ H.map f
  apply (cancel_epi (F.map (e X).hom)).1
  apply (cancel_mono (H.map (e Y).inv)).1
  dsimp only [F, H, Functor.comp_obj] at *
  simpa only [Functor.map_comp, Functor.map_inv, Category.assoc,
    Iso.map_hom_inv_id_assoc, Iso.map_hom_inv_id, Functor.comp_obj,
    Category.comp_id]
    using hn.symm

end SheafOfModules.PrincipalReduction.Setup
