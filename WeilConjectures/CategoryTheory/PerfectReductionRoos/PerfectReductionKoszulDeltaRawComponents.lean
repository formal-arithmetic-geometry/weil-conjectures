/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns

/-! Componentwise invertibility of the raw finite Koszul/Roos comparison.

Source: Bhatt--Scholze, Lemma 3.5.5 (blueprint: new-lem-sp-perfect-reduction-koszul-raw-components).
The proof is the finite product calculation: tensoring a countable Roos product with either
unit term of the two-term Koszul complex is an isomorphism, and the two coordinate formulas
identify each degree component with the resulting biproduct of these maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings
namespace CategoryTheory.PerfectReductionRoos
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

attribute [local instance] SheafOfModules.monoidalCategory

private def twoTermLeftRawIso (K Q : CochainComplex (TotalTensorSigns.Modules R) ℤ)
    (hz : ∀ p : ℤ, p ≠ -1 → p ≠ 0 → IsZero (K.X p)) (n : ℤ) :
    (((total R).obj K).obj Q).X n ≅
      (K.X (-1) ⊗ Q.X (n + 1)) ⊞ (K.X 0 ⊗ Q.X n) := by
  classical
  let f := fun (p q : ℤ) (hpq : p + q = n) ↦
    if hp : p = -1 then
      eqToHom (congrArg₂ (fun i k ↦ K.X i ⊗ Q.X k) hp
        (show q = n + 1 by omega)) ≫ biprod.inl
    else if hp' : p = 0 then
      eqToHom (congrArg₂ (fun i k ↦ K.X i ⊗ Q.X k) hp'
        (show q = n by omega)) ≫ biprod.inr
    else 0
  refine ⟨HomologicalComplex.mapBifunctorDesc
      (K₁ := K) (K₂ := Q) (F := tensor R) (c := .up ℤ) f,
    biprod.desc (ι R K Q (-1) (n + 1) n (by omega))
      (ι R K Q 0 n n (by simp)), ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hp : p = -1
    · subst p
      obtain rfl : q = n + 1 := by omega
      simp only [f, dif_pos rfl, eqToHom_refl, Category.id_comp, biprod.inl_desc]
      exact (Category.comp_id _).symm
    · by_cases hp' : p = 0
      · subst p
        obtain rfl : q = n := by omega
        simp only [f, dif_neg (by omega : (0 : ℤ) ≠ -1), dite_true,
          eqToHom_refl, Category.id_comp, biprod.inr_desc]
        exact (Category.comp_id _).symm
      · exact (((tensor R).flip.obj (Q.X q)).map_isZero (hz p hp hp')).eq_of_src _ _
  · apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc, f,
        dite_true, eqToHom_refl, Category.id_comp, Category.comp_id, ι]
    · simp only [biprod.inr_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc, f,
        dif_neg (by omega : (0 : ℤ) ≠ -1), dite_true, eqToHom_refl,
        Category.id_comp, Category.comp_id, ι]

private def twoTermLeftIso (K Q : CochainComplex (TotalTensorSigns.Modules R) ℤ)
    (hz : ∀ p : ℤ, p ≠ -1 → p ≠ 0 → IsZero (K.X p))
    (eNeg : K.X (-1) ≅ 𝟙_ (TotalTensorSigns.Modules R))
    (eZero : K.X 0 ≅ 𝟙_ (TotalTensorSigns.Modules R)) (n : ℤ) :
    (((total R).obj K).obj Q).X n ≅ Q.X (n + 1) ⊞ Q.X n :=
  twoTermLeftRawIso R K Q hz n ≪≫ biprod.mapIso
    ((eNeg ⊗ᵢ Iso.refl _) ≪≫ λ_ _) ((eZero ⊗ᵢ Iso.refl _) ≪≫ λ_ _)

private def productBiprodIso
    (X Y : ℕ → TotalTensorSigns.Modules R) :
    (∏ᶜ fun j ↦ X j ⊞ Y j) ≅ (∏ᶜ X) ⊞ (∏ᶜ Y) where
  hom := biprod.lift
    (Pi.lift fun j ↦ Pi.π _ j ≫ biprod.fst)
    (Pi.lift fun j ↦ Pi.π _ j ≫ biprod.snd)
  inv := Pi.lift fun j ↦ biprod.map (Pi.π X j) (Pi.π Y j)
  hom_inv_id := by
    apply Pi.hom_ext
    intro j
    apply biprod.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply Pi.hom_ext
      intro j
      simp [Category.assoc]
    · apply Pi.hom_ext
      intro j
      simp [Category.assoc]

private def productEvalIso
    (P : CochainComplex (ℕᵒᵖ ⥤ TotalTensorSigns.Modules R) ℤ) (n : ℤ) :
    (roosP P).X n ≅ ∏ᶜ fun j : ℕ ↦ (P.asFunctor.obj (op j)).X n :=
  asIso (piComparison (HomologicalComplex.eval _ (.up ℤ) n)
    (fun j : ℕ ↦ P.asFunctor.obj (op j)))

private def roosDegreeIso
    (P : CochainComplex (ℕᵒᵖ ⥤ TotalTensorSigns.Modules R) ℤ) (n : ℤ) :
    (roosF.obj P).X (n + 1) ≅
      (∏ᶜ fun j : ℕ ↦ (P.asFunctor.obj (op j)).X n) ⊞
      (∏ᶜ fun j : ℕ ↦ (P.asFunctor.obj (op j)).X (n + 1)) :=
  roosχ P n ≪≫ biprod.mapIso (productEvalIso R P n) (productEvalIso R P (n + 1))

private def koszulNegIso (m : ℕ) :
    (principalKoszul R t m).X (-1) ≅ 𝟙_ (TotalTensorSigns.Modules R) := by
  let S := (HomologicalComplex.single (TotalTensorSigns.Modules R) (.up ℤ) 0).obj
    (𝟙_ (TotalTensorSigns.Modules R))
  have hz : IsZero (S.X (-1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  exact HomologicalComplex.homotopyCofiber.XIsoBiprod
      (principalKoszulScalarComplex R t m) (-1) 0 (by decide) ≪≫
    (isoBiprodZero hz).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

private def koszulZeroIso (m : ℕ) :
    (principalKoszul R t m).X 0 ≅ 𝟙_ (TotalTensorSigns.Modules R) := by
  let S := (HomologicalComplex.single (TotalTensorSigns.Modules R) (.up ℤ) 0).obj
    (𝟙_ (TotalTensorSigns.Modules R))
  have hz : IsZero (S.X 1) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  exact HomologicalComplex.homotopyCofiber.XIsoBiprod
      (principalKoszulScalarComplex R t m) 0 1 rfl ≪≫
    (isoZeroBiprod hz).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

private theorem koszulZeroOutside (m : ℕ) (p : ℤ) (hp : p ≠ -1) (hp' : p ≠ 0) :
    IsZero ((principalKoszul R t m).X p) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ p).2
  constructor
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hp'

private def signedShuffle (A B D E : TotalTensorSigns.Modules R) :
    (A ⊞ B) ⊞ (D ⊞ E) ≅ (A ⊞ D) ⊞ (B ⊞ E) where
  hom := biprod.lift
    (biprod.lift (-(biprod.fst ≫ biprod.fst)) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  inv := biprod.lift
    (biprod.lift (-(biprod.fst ≫ biprod.fst)) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  hom_inv_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [Category.assoc]

private def sourceDegreeIso (m : ℕ)
    (P : CochainComplex (ℕᵒᵖ ⥤ TotalTensorSigns.Modules R) ℤ) (n : ℤ) :=
  twoTermLeftIso R (principalKoszul R t m) (roosF.obj P)
    (koszulZeroOutside R t m) (koszulNegIso R t m) (koszulZeroIso R t m) (n + 1) ≪≫
    biprod.mapIso (roosDegreeIso R P (n + 1)) (roosDegreeIso R P n)

private def targetDegreeIso (m : ℕ)
    (P : CochainComplex (ℕᵒᵖ ⥤ TotalTensorSigns.Modules R) ℤ) (n : ℤ) :=
  roosDegreeIso R (tensorTower R (principalKoszul R t m) P) n ≪≫ biprod.mapIso
    (Pi.mapIso (fun j : ℕ ↦ twoTermLeftIso R (principalKoszul R t m)
      (P.asFunctor.obj (op j)) (koszulZeroOutside R t m)
      (koszulNegIso R t m) (koszulZeroIso R t m) n) ≪≫ productBiprodIso R _ _)
    (Pi.mapIso (fun j : ℕ ↦ twoTermLeftIso R (principalKoszul R t m)
      (P.asFunctor.obj (op j)) (koszulZeroOutside R t m)
      (koszulNegIso R t m) (koszulZeroIso R t m) (n + 1)) ≪≫
        productBiprodIso R _ _)

set_option maxHeartbeats 2000000 in
-- Expanding the four product coordinates requires repeated tensor and biproduct normalization.
/-- Each degree component is the signed permutation of four finite product summands.
Source: Bhatt--Scholze, Lemma 3.5.5
(blueprint: new-lem-sp-perfect-reduction-koszul-raw-components). -/
theorem koszulDeltaRaw_component_isIso
    (r : KoszulDeltaRawData R t) :
    ∀ m P n, IsIso ((r.hom m P).f n) := by
  intro m P n
  obtain ⟨n, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective n
  let a := sourceDegreeIso R t m P n
  let b := targetDegreeIso R t m P n
  let e := a ≪≫ signedShuffle R _ _ _ _ ≪≫ b.symm
  have h : (r.hom m P).f (n + 1) = e.hom := by
    apply (cancel_mono b.hom).1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n + 1 at hpq
    by_cases hp : p = -1
    · subst p
      obtain rfl : q = n + 1 + 1 := by omega
      have hs (j : ℕ) := reassoc_of% r.shifted m P (n + 1) (-1) n (by omega) j
      have hu (j : ℕ) := reassoc_of% r.unshifted m P (n + 1) (-1) n (by omega) j
      dsimp only [ι] at hs hu
      apply biprod.hom_ext <;> apply biprod.hom_ext <;> apply Pi.hom_ext <;> intro j
      all_goals simp [e, a, b, sourceDegreeIso, targetDegreeIso, signedShuffle,
        productBiprodIso, roosDegreeIso, twoTermLeftIso, twoTermLeftRawIso,
        Category.assoc, ι, hs, hu, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    · by_cases hp' : p = 0
      · subst p
        obtain rfl : q = n + 1 := by omega
        have hs (j : ℕ) := reassoc_of% r.shifted m P n 0 n (by omega) j
        have hu (j : ℕ) := reassoc_of% r.unshifted m P n 0 n (by omega) j
        dsimp only [ι] at hs hu
        apply biprod.hom_ext <;> apply biprod.hom_ext <;> apply Pi.hom_ext <;> intro j
        all_goals simp [e, a, b, sourceDegreeIso, targetDegreeIso, signedShuffle,
          productBiprodIso, roosDegreeIso, twoTermLeftIso, twoTermLeftRawIso,
          Category.assoc, ι, hs, hu, HomologicalComplex.ι_mapBifunctorDesc_assoc]
      · exact (((tensor R).flip.obj ((roosF.obj P).X q)).map_isZero
          (koszulZeroOutside R t m p hp hp')).eq_of_src _ _
  change IsIso ((r.hom m P).f (n + 1))
  rw [h]
  exact e.isIso_hom

end CategoryTheory.PerfectReductionRoos
