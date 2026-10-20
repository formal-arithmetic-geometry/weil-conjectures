/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.Paper.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.Paper.CompatibleFiniteDerivedTrivializations
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower
import Sheaf.Paper.FiniteMittagLeffler
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Limits
import Sheaf.Paper.CompletedConstantFiniteComplexRealization
import Sheaf.Paper.BoundedConstructibleTower
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups

/-! # Reconstruction of a lisse normalized tower

Source: Stacks Project and the local-effectivity argument in amplification (c).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem transport_normalization_in_image
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {A' : Type u₃} [Category.{v₃} A'] {B' : Type u₄} [Category.{v₄} B']
    (F : A ⥤ A') (G : B ⥤ B') [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    (R : A ⥤ B) (R' : A' ⥤ B') (e : R ⋙ G ≅ F ⋙ R')
    {X : B} {Y : A} (t : X ⟶ R.obj Y) (Z : A)
    (ht : Function.Bijective (fun k : Y ⟶ Z ↦ t ≫ R.map k)) :
    Function.Bijective (fun k : F.obj Y ⟶ F.obj Z ↦
      G.map t ≫ e.hom.app Y ≫ R'.map k) := by
  let φ := fun k : F.obj Y ⟶ F.obj Z ↦ G.map t ≫ e.hom.app Y ≫ R'.map k
  apply (Function.Bijective.of_comp_iff φ
    ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective Y Z)).1
  have hG := (Functor.FullyFaithful.ofFullyFaithful G).map_bijective X (R.obj Z)
  have hc : Function.Bijective (fun k : G.obj X ⟶ G.obj (R.obj Z) ↦ k ≫ e.hom.app Z) :=
    ⟨fun _ _ h ↦ (cancel_mono (e.hom.app Z)).1 h,
      fun k ↦ ⟨k ≫ e.inv.app Z, by simp⟩⟩
  have h := hc.comp (hG.comp ht)
  have he (k : Y ⟶ Z) :
      φ (F.map k) = G.map (t ≫ R.map k) ≫ e.hom.app Z := by
    dsimp [φ]
    rw [G.map_comp, Category.assoc]
    exact congrArg (fun f ↦ G.map t ≫ f) (e.hom.naturality k).symm
  change Function.Bijective (fun k : Y ⟶ Z ↦ φ (F.map k))
  simp only [he]
  exact h

private theorem transport_normalization
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {A' : Type u₃} [Category.{v₃} A'] {B' : Type u₄} [Category.{v₄} B']
    (F : A ⥤ A') (G : B ⥤ B') [F.IsEquivalence] [G.Full] [G.Faithful]
    (R : A ⥤ B) (R' : A' ⥤ B') (e : R ⋙ G ≅ F ⋙ R')
    {X : B} {Y : A} (t : X ⟶ R.obj Y)
    (ht : ∀ Z : A, Function.Bijective (fun k : Y ⟶ Z ↦ t ≫ R.map k)) :
    ∀ Z : A', Function.Bijective (fun k : F.obj Y ⟶ Z ↦
      G.map t ≫ e.hom.app Y ≫ R'.map k) := by
  intro Z
  let Z₀ := F.objPreimage Z
  let i : F.obj Z₀ ≅ Z := F.objObjPreimageIso Z
  have h := transport_normalization_in_image F G R R' e t Z₀ (ht Z₀)
  constructor
  · intro k l hkl
    apply (cancel_mono i.inv).1
    apply h.1
    simpa only [R'.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ R'.map i.inv) hkl
  · intro f
    obtain ⟨k, hk⟩ := h.2 (f ≫ R'.map i.inv)
    refine ⟨k ≫ i.hom, ?_⟩
    dsimp only at hk ⊢
    rw [R'.map_comp]
    calc
      _ = (G.map t ≫ e.hom.app Y ≫ R'.map k) ≫ R'.map i.hom := by
        simp only [Category.assoc]
      _ = (f ≫ R'.map i.inv) ≫ R'.map i.hom :=
        congrArg (fun a ↦ a ≫ R'.map i.hom) hk
      _ = f := by rw [Category.assoc, ← R'.map_comp, i.inv_hom_id, R'.map_id,
        Category.comp_id]

private theorem universal_arrow_iff_bijective
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (R : A ⥤ B) {X : B} {Y : A} (t : X ⟶ R.obj Y) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk t)) ↔
      ∀ Z : A, Function.Bijective (fun k : Y ⟶ Z ↦ t ≫ R.map k) := by
  constructor
  · rintro ⟨h⟩ Z
    exact ⟨fun k l hkl ↦ h.hom_ext hkl,
      fun f ↦ ⟨h.desc (StructuredArrow.mk f), h.fac _⟩⟩
  · intro h
    classical
    let lift (Z : StructuredArrow X R) : StructuredArrow.mk t ⟶ Z :=
      StructuredArrow.homMk ((h Z.right).surjective Z.hom).choose
        ((h Z.right).surjective Z.hom).choose_spec
    refine ⟨CategoryTheory.Limits.IsInitial.ofUniqueHom lift ?_⟩
    intro Z k
    apply StructuredArrow.hom_ext
    apply (h Z.right).injective
    exact k.w.trans ((h Z.right).surjective Z.hom).choose_spec.symm

private theorem exists_boundedFinite_model {R : Type r} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) (hC : DerivedCategory.IsPseudoCoherent C)
    (hvan : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite R (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ C) := by
  obtain ⟨E, c, hc, hfiniteE, ⟨eE⟩⟩ := hC
  have : (DerivedCategory.Q.obj E).IsLE b := (DerivedCategory.isLE_iff _ _).2
    fun i hi ↦ (hvan i (Or.inr hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso eE)
  have : E.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  let P := E.truncLE b
  let e : DerivedCategory.Q.obj P ≅ C :=
    asIso (DerivedCategory.Q.map (E.ιTruncLE b)) ≪≫ eE
  have hfinite (i : ℤ) : Module.Finite R (P.X i) := by
    obtain hi | rfl | hi := lt_trichotomy i b
    · have : Module.Finite R (E.X i) := (hfiniteE i).2
      exact Module.Finite.equiv (E.truncLEXIso b i hi).toLinearEquiv.symm
    · have : Module.Finite R (E.X i) := (hfiniteE i).2
      have : Module.Finite R (E.cycles i) :=
        Module.Finite.of_injective (E.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      exact Module.Finite.equiv (E.truncLEXIsoCycles i).toLinearEquiv.symm
    · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.1
        (CochainComplex.isZero_of_isStrictlyLE P b i hi)
      infer_instance
  have : (DerivedCategory.Q.obj P).IsGE a := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦
    (hvan i (Or.inl hi)).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have : P.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  let L := P.truncGE a
  refine ⟨L, ?_, ?_, ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ e⟩⟩
  · intro i hi
    rcases hi with hi | hi
    · exact L.isZero_of_isStrictlyGE a i hi
    · exact L.isZero_of_isStrictlyLE b i hi
  · intro i
    obtain hi | rfl | hi := lt_trichotomy i a
    · have : Subsingleton ((P.truncGE a).X i) :=
        ModuleCat.isZero_iff_subsingleton.1
          (CochainComplex.isZero_of_isStrictlyGE _ a i hi)
      infer_instance
    · have : Module.Finite R (P.X i) := hfinite i
      have : Module.Finite R (P.opcycles i) :=
        Module.Finite.of_surjective (P.pOpcycles i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      exact Module.Finite.equiv (P.truncGEXIsoOpcycles i).toLinearEquiv.symm
    · have : Module.Finite R (P.X i) := hfinite i
      exact Module.Finite.equiv (P.truncGEXIso a i hi).toLinearEquiv.symm

private theorem map_roos {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (K : ℕ → C) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    (f : ∀ n, K (n + 1) ⟶ K n) :
    F.map (towerTransitionEndomorphism f) ≫ piComparison F K =
      piComparison F K ≫ towerTransitionEndomorphism (fun n ↦ F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, towerTransitionEndomorphism,
    towerProductShift, Preadditive.sub_comp, Category.id_comp, Pi.lift_π,
    Preadditive.comp_sub, ← F.map_comp, F.map_sub]
  congr 1
  rw [← Category.assoc, piComparison_comp_π]
  exact F.map_comp _ _

private theorem module_roos_epi {R : Type r} [CommRing R]
    (K : ℕᵒᵖ ⥤ ModuleCat.{r} R) (hfinite : ∀ n, Finite (K.obj n)) :
    Epi (towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)) := by
  let F := forget₂ (ModuleCat.{r} R) AddCommGrpCat.{r}
  let B := K ⋙ F
  obtain ⟨_, e, _⟩ := derivedLimitRoosAbelianGroups.2
  have hz : IsZero (cokernel (roosMap B)) :=
    ((finiteTower_mittagLeffler_vanishing B hfinite).2).of_iso (e B).symm
  have : Epi (roosMap B) := Preadditive.epi_of_isZero_cokernel _ hz
  let t := towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
    (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
  let c := PreservesProduct.iso F (fun n ↦ K.obj (op n))
  have he : F.map t = c.hom ≫ roosMap B ≫ c.inv := by
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact map_roos F _ _
  have : Epi (F.map t) := by rw [he]; infer_instance
  exact (ModuleCat.epi_iff_surjective _).2
    ((AddCommGrpCat.epi_iff_surjective (F.map t)).1 inferInstance)

private theorem module_derivedLimit_interval {R : Type r} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{r} R)]
    (K : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{r} R))
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory (ModuleCat.{r} R))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (a b : ℤ)
    (hfinite : ∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj n)))
    (hbounded : ∀ (n : ℕᵒᵖ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj n))) :
    ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj L) := by
  obtain ⟨hP, _, hH⟩ := derivedCategory_countableProducts_core (ModuleCat.{r} R)
  let _ := hP
  intro i hi
  let H := DerivedCategory.homologyFunctor (ModuleCat.{r} R) (i - 1)
  have := hH ℕ (i - 1)
  have := hH ℕ i
  let t := towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
    (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
  have hep : Epi (towerTransitionEndomorphism (K := fun n ↦ H.obj (K.obj (op n)))
      (fun n ↦ H.map (K.map (homOfLE (Nat.le_succ n)).op))) :=
    module_roos_epi (K ⋙ H) (fun n ↦ hfinite n (i - 1))
  let c := PreservesProduct.iso H (fun n ↦ K.obj (op n))
  have he : H.map t = c.hom ≫
      towerTransitionEndomorphism (K := fun n ↦ H.obj (K.obj (op n)))
        (fun n ↦ H.map (K.map (homOfLE (Nat.le_succ n)).op)) ≫
        c.inv := by
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact map_roos H _ _
  have : Epi (H.map t) := by rw [he]; infer_instance
  let T := Pretriangulated.Triangle.mk p t δ
  have hepT : Epi (H.map T.mor₂) := by
    change Epi (H.map t)
    infer_instance
  have hzδ : DerivedCategory.HomologySequence.δ T (i - 1) i = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT (i - 1) i).1
      inferInstance
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).map p) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i).2 hzδ
  have hz : IsZero (∏ᶜ fun n : ℕ ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj (op n))) :=
    (limit.isLimit _).isZero_pt
      ((Discrete.functor (fun n : ℕ ↦
        (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj (op n)))).isZero
          (fun n ↦ hbounded (op n.as) i hi))
  have hzprod := hz.of_iso
    (PreservesProduct.iso (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i)
      (fun n ↦ K.obj (op n)))
  exact hzprod.of_mono ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).map p)

private theorem exists_boundedFinite_normalizedTower
    {C : Type r} [CommRing C] [IsNoetherianRing C]
    (J : Ideal C) [IsAdicComplete J C]
    [HasDerivedCategory.{w} (ModuleCat.{r} C)]
    [∀ n : ℕ, HasDerivedCategory.{w} (ModuleCat.{r} (C ⧸ J ^ (n + 1)))]
    [∀ n : ℕ, Finite (C ⧸ J ^ (n + 1))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj (K n))
    (hnorm : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1)))),
      Function.Bijective (fun a : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map a))
    (f : ∀ n : ℕ,
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.obj
        (K (n + 1)) ⟶
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))
    (hf : ∀ n : ℕ, f n =
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
        (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2))))).inv.app (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{r}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n))
    (a b : ℤ)
    (hbounded : ∀ (n : ℕ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n + 1))) i).obj (K n)))
    (hfinite : ∀ (n : ℕ) (i : ℤ), Module.Finite (C ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n + 1))) i).obj (K n))) :
    ∃ E : DerivedCategory (ModuleCat.{r} C),
      (∃ P : CochainComplex (ModuleCat.{r} C) ℤ,
        (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
        (∀ i : ℤ, Module.Finite C (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ E)) ∧
      ∀ (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{r} C) ⥤
          DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1))))
        (adj : ∀ n : ℕ, L n ⊣
          (ModuleCat.restrictScalars.{r}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory),
        ∃ e : ∀ n : ℕ, (L n).obj E ≅ K n,
          ∀ (m n : ℕ) (h : n ≤ m),
            (adj m).unit.app E ≫
              (ModuleCat.restrictScalars.{r}
                (Ideal.Quotient.mk (J ^ (m + 1)))).mapDerivedCategory.map
                (e m).hom ≫
              (Functor.ofOpSequence (X := fun k : ℕ ↦
                (ModuleCat.restrictScalars.{r}
                  (Ideal.Quotient.mk (J ^ (k + 1)))).mapDerivedCategory.obj (K k))
                f).map (homOfLE h).op =
            (adj n).unit.app E ≫
              (ModuleCat.restrictScalars.{r}
                (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
                (e n).hom := by
  classical
  let R (n : ℕ) := ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 1)))
  let D := Functor.ofOpSequence (X := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f
  obtain ⟨hP, _, _⟩ := derivedCategory_countableProducts_core.{0, w, r, r + 1}
    (ModuleCat.{r} C)
  let _ := hP
  obtain ⟨E, p, δ, hE⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f)
  have hT : IsDerivedLimitTriangle
      (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f E p δ := hE
  have hrec := DerivedCategory.pseudoCoherent_normalizedAlgebraTower J K t hnorm f hf
    E p δ hT ⟨b, fun i hi ↦ hbounded 0 i (Or.inr hi)⟩ (hfinite 0)
  have hfin : ∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj (D.obj n)) := by
    intro n i
    have : Module.Finite (C ⧸ J ^ (n.unop + 1))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) := hfinite n.unop i
    have : Finite ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) :=
      Module.finite_of_finite (C ⧸ J ^ (n.unop + 1))
    let e := ((R n.unop).mapDerivedCategoryHomologyFunctorIso i).app (K n.unop)
    change Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj
      ((R n.unop).mapDerivedCategory.obj (K n.unop)))
    exact Finite.of_equiv ((DerivedCategory.homologyFunctor
      (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) e.toLinearEquiv.toEquiv
  have hvan : ∀ (n : ℕᵒᵖ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj (D.obj n)) := by
    intro n i hi
    exact (R n.unop).isZero_homologyFunctor_mapDerivedCategory_obj (hbounded n.unop i hi)
  have hDT : IsDerivedLimitTriangle
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) E p δ := by
    simpa only [D, Functor.ofOpSequence_map_homOfLE_succ] using hT
  refine ⟨E, exists_boundedFinite_model E a b hrec.1
    (module_derivedLimit_interval D E p δ hDT a b hfin hvan), ?_⟩
  intro L adj
  obtain ⟨e, _, hc, _, _⟩ := hrec.2 L adj
  exact ⟨e, hc⟩

private theorem completion_eval_ker {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  ext x
  trans x ∈ (AdicCompletion.eval I A n).ker
  · change AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0
    let h : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
    have hi : Function.Injective (Ideal.Quotient.factor h.le) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le h.ge
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x h.le]
    exact map_eq_zero_iff (Ideal.Quotient.factor h.le) hi
  · rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, ← Ideal.map_pow]
    change x ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I A)) ↔
      x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A))
    rw [Ideal.smul_top_eq_map]
    rfl

private noncomputable def completionQuotientEquiv {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    (AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ n) ≃+*
      (A ⧸ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq A (completion_eval_ker I hI n).symm).toRingEquiv.trans
    ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ I n))

private theorem completionQuotientEquiv_mk {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    completionQuotientEquiv I hI n (Ideal.Quotient.mk _ x) =
      AdicCompletion.evalₐ I n x := by
  simp [completionQuotientEquiv]

private theorem completion_eval_factor {A : Type u} [CommRing A]
    (I : Ideal A) {m n : ℕ} (h : n ≤ m) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I m x) =
      AdicCompletion.evalₐ I n x := by
  let hm : (I ^ m • ⊤ : Ideal A) = I ^ m := by simp
  let hn : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hm.le,
    ← AdicCompletion.factor_eval_eq_evalₐ I x hn.le]
  have he := AdicCompletion.transitionMap_comp_eval_apply I A h x
  change Submodule.factor _ (AdicCompletion.eval I A m x) =
    AdicCompletion.eval I A n x at he
  rw [← he]
  generalize AdicCompletion.eval I A m x = y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

private theorem completionQuotientEquiv_factor {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {m n : ℕ} (h : n ≤ m)
    (x : AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ m) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (completionQuotientEquiv I hI m x) =
      completionQuotientEquiv I hI n
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [completionQuotientEquiv_mk, Ideal.Quotient.factor_mk, completionQuotientEquiv_mk]
  exact completion_eval_factor I h x

/-- On an immersed stratum where all finite reductions are lisse, the normalized
tower has a single bounded completed-coefficient model on a pro-etale cover.
This statement starts after stratification and asserts no global constructibility.

Source: Stacks Project, proetale.tex, Tag 09BV and more-algebra.tex, Tag 09AV;
steps 4--8 of the local-effectivity argument
(blueprint: lem-weil-pbc-lisse-normalized-tower-local-models).

Proof: identify the inverse images of the finite constant coefficient sheaves with
the constant coefficient sheaves on Y, and hence identify the inverse images of
the finite function coefficient sheaves with their canonical presentations on Y.
Transport the restricted levels along these isomorphisms. The proved helpers
transport_normalization_in_image and transport_normalization preserve the
universal Hom bijections under fully faithful coefficient functors and
equivalences; universal_arrow_iff_bijective identifies these bijections with
the structured-arrow normalization witnesses. Their cohomology is
finite lisse, so the single whole-scheme stratum witnesses constructibility.
Apply finiteCoefficient_constructibleDerived_origin_presentation on Y to obtain
bounded constructible etale sources K_n. The interval [a,b] is retained because
inverse image is exact and the etale/pro-etale comparison detects zero sheaves.
Tensor-pullback identifies the
comparison of each derived etale reduction with the normalized restricted level.
Check boundedness of that reduction by exact cohomology comparison and detection
of zero before applying bounded-below full faithfulness. Lift both directions of
each normalization and each restricted transition uniquely. Faithfulness then
gives their quotient cocycle. This constructs the normalized etale tower needed
by compatible_finite_derived_trivializations; it makes no finite-Tor assumption.
Cover the Noetherian stratum by its finitely many connected components.
At a geometric point of a nonempty component take the derived stalks E_n.
Exactness and tensor-pullback give finite cohomology in [a,b] and the supplied
normalizations. Finite-ring-derived-local-constancy and compatible-finite-derived-
trivializations give a pro-etale cover and compatible constant identifications
of every level with E_n. Restrict their scalars to the completion C and form
their homotopy limit E. The proved completion_eval_ker and
completionQuotientEquiv helpers identify every power quotient of C with A/I^n;
completionQuotientEquiv_factor proves compatibility with every quotient transition.
Take the product of the restricted E_n, form one minus
the transition shift, and complete it to a distinguished triangle. Its shifted
cone and first arrow give the required derived-limit triangle and projections.
The proved helper exists_boundedFinite_normalizedTower assembles this algebraic
construction. It applies pseudoCoherent_normalizedAlgebraTower to the triangle
and retains its projection-induced reduction isomorphisms and compatibility. The private helper
module_derivedLimit_interval proves vanishing outside [a,b]
directly in the module category: homology commutes with the countable product,
the finite-group Mittag--Leffler theorem makes the preceding Roos operator
surjective, and the long exact sequence embeds each outside cohomology module
into a zero product. This avoids transporting a derived triangle to abelian groups.
The proved private helper
exists_boundedFinite_model supplies a bounded finite representative directly from
pseudo-coherence: truncate its finite free model above b, using the finite kernel
of the top differential over the Noetherian ring. Then truncate at a by replacing
the a-th term by the finite cokernel of the incoming differential. Both truncation
maps are quasi-isomorphisms by the cohomological bounds, giving a bounded finite
complex Q. Realize Q
termwise by completed_constant_finite_complex_realization, using its relative
clause for the inverse image of the completion on X. Finite terms give adic
lissity and the finite reductions give finite-lisse cohomology. Compose the
realization comparisons
with the compatible trivializations
to get isomorphisms from the realized reductions to the restricted tower.
Their two naturality squares give the displayed forward semilinear square.
Inverting this square is left to the caller. Generate a covering
sieve from the composite covers and restrict these models to its arrows;
exact pullback preserves the bounds, terms and compatibility. Empty components
contribute the empty covering sieve. No projectivity of the truncated first
term and no finite Tor dimension are used. -/
theorem lisseNormalizedTower_local_models
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    ∃ V : Sieve (⊤_ Y.ProEt), V ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), V f →
        ∃ L : CochainComplex (pbcModules U.left
            ((adicTowerInverseImage (U.hom ≫ g)).obj (pbcAdicCompletion X d))) ℤ,
          (∀ q : ℤ, (q < a ∨ b < q) → IsZero (L.X q)) ∧
          (∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ (U.hom ≫ g) A _
            d.noetherian d.ideal
            ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
              (pbcCompletedComparison X d).hom)).obj (L.X q))) ∧
          (∀ (n : ℕ) (q : ℤ),
            IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
              ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                (pbcLevelConstantComparison X d n).hom)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj
                    (adicTowerLocalReduction d (U.hom ≫ g) L n)))) ∧
          ∃ e : ∀ n : ℕ, adicTowerLocalReduction d (U.hom ≫ g) L n ≅
              (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                (M.level n),
            ∀ (m n : ℕ) (hnm : n ≤ m),
              (e m).hom ≫ adicTowerRestrictedTransition d (U.hom ≫ g) M m n hnm =
                adicTowerLocalTransition d (U.hom ≫ g) L m n hnm ≫
                  (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcAdicQuotient X d m n hnm))).map (e n).hom := by sorry

end AlgebraicGeometry.Scheme
