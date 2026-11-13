/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.GlobalSectionOrderedCechTensor
import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarKFlatQuasiIso

/-! # The localization tensor model after scalar extension from global sections

## References

* Stacks Project, Tags 0996, 099D(d) and 099E.
-/

@[expose] public section
set_option autoImplicit false
universe u w wA
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive

private theorem ringFlat_of_point_flat {A : Type u} [CommRing A]
    (M : RingSiteModules A)
    (hM : Module.Flat A (M.val.obj (op ⟨PUnit.unit⟩))) :
    SheafOfModules.IsFlat M := by
  let R := CochainComplex.onePointRingSheaf A
  let O := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  have hflat (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
      Module.Flat (R.obj.obj V) (M.val.obj V) := by
    obtain rfl : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
    exact hM
  have hP : PreservesFiniteLimits (MonoidalCategory.tensorRight M.val) := by
    constructor
    intro K _ _
    have (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
        Module.Flat (R.obj.obj V) (M.val.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (MonoidalCategory.tensorRight (show ModuleCat (R.obj.obj V) from M.val.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective ⊥ _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective ⊥ _ (fun _ ↦ Function.surjective_id)
  have hs := (PresheafOfModules.isFlat_sheafification_obj
    (R := R) (𝟙 O.obj) M.val hP).2
  let e := asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit.app M)
  let := SheafOfModules.monoidalCategory R
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e) hs

private theorem ring_isZero_of_point {A : Type u} [CommRing A]
    (M : RingSiteModules A) [Subsingleton (M.val.obj (op ⟨PUnit.unit⟩))] :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply SheafOfModules.hom_ext
  ext V : 1
  obtain rfl : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
  ext x
  exact Subsingleton.elim _ _

private theorem ordered_coordinates_kflat (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin r → A) (K : CochainComplex (RingSiteModules A) ℤ)
    (e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
    (e : ∀ q : ℕ, (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
    (hneg : ∀ n : ℤ, n < 0 → IsZero (K.X n)) :
    K.IsKFlatIndependentCoefficients := by
  classical
  change K.IsKFlatTensor
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨r, fun n hn ↦ ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := by
      refine ⟨(n - 1).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    subst n
    have ht : IsEmpty (Fin (q + 1) ↪o Fin r) := by
      refine ⟨fun t ↦ ?_⟩
      have := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at this
      omega
    let := ht
    have : Subsingleton ((K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩)) :=
      (e q).injective.subsingleton
    exact ring_isZero_of_point _
  · intro n
    by_cases hn : n < 0
    · have hz := (SheafOfModules.evaluation
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)).map_isZero (hneg n hn)
      have : Subsingleton ((K.X n).val.obj (op ⟨PUnit.unit⟩)) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact ringFlat_of_point_flat _ inferInstance
    · by_cases hn₀ : n = 0
      · subst n
        exact ringFlat_of_point_flat _ (Module.Flat.of_linearEquiv e₀)
      · obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := by
          refine ⟨(n - 1).toNat, ?_⟩
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        subst n
        have (t : Fin (q + 1) ↪o Fin r) :
            Module.Flat A (Localization.Away (∏ i, f (t i))) := inferInstance
        exact ringFlat_of_point_flat _ (Module.Flat.of_linearEquiv
          ((e q).trans DFinsupp.linearEquivFunOnFintype.symm))

private theorem augmented_iso_of_good_quasiIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (good : CochainComplex A ℤ → Prop)
    (hres : ∀ Z : CochainComplex A ℤ,
      ∃ (W : CochainComplex A ℤ) (q : W ⟶ Z), good W ∧ QuasiIso q)
    (hF : ∀ {K L : CochainComplex A ℤ} (t : K ⟶ L),
      good K → good L → QuasiIso t →
        QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map t))
    (K L U : CochainComplex A ℤ) (a : K ⟶ U) (b : L ⟶ U)
    (hK : good K) (hL : good L)
    (α : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L)
    (hα : α.hom ≫ DerivedCategory.Q.map b = DerivedCategory.Q.map a) :
    ∃ e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L),
      e.hom ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map b) =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  classical
  obtain ⟨Z, s, hs, t, he⟩ := DerivedCategory.right_fac α.hom
  let := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  have htiso : IsIso (DerivedCategory.Q.map t) := by
    have ht : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ α.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [ht]
    infer_instance
  have ht' : QuasiIso t :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 htiso
  have hst : DerivedCategory.Q.map (s ≫ a) = DerivedCategory.Q.map (t ≫ b) := by
    simp only [Functor.map_comp]
    rw [← hα, ← Category.assoc, he, IsIso.hom_inv_id_assoc]
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hh : DerivedCategory.Qh.map (H.map (s ≫ a)) =
      DerivedCategory.Qh.map (H.map (t ≫ b)) := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app U)).1
    simp only [H, DerivedCategory.quotientCompQhIso_hom_naturality, hst]
  obtain ⟨V, v, hv, hcomm⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) _ _).1 hh
  obtain ⟨V, rfl⟩ := HomotopyCategory.quotient_obj_surjective V
  obtain ⟨v, rfl⟩ := H.map_surjective v
  have hv' : QuasiIso v :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff v).1 hv
  have hhom : Homotopy (v ≫ s ≫ a) (v ≫ t ≫ b) :=
    HomotopyCategory.homotopyOfEq _ _ (by
      simpa only [Functor.map_comp, Category.assoc] using hcomm)
  obtain ⟨W, q, hW, hq⟩ := hres V
  let := hs'
  let := ht'
  let := hv'
  let := hq
  let u := q ≫ v ≫ s
  let z := q ≫ v ≫ t
  have hu : QuasiIso u := inferInstance
  have hz : QuasiIso z := inferInstance
  let T := F.mapHomologicalComplex (.up ℤ)
  have hTu : QuasiIso (T.map u) := hF u hW hK hu
  have hTz : QuasiIso (T.map z) := hF z hW hL hz
  let := hTu
  let := hTz
  let e := (asIso (DerivedCategory.Q.map (T.map u))).symm ≪≫
    asIso (DerivedCategory.Q.map (T.map z))
  refine ⟨e, ?_⟩
  apply (cancel_epi (DerivedCategory.Q.map (T.map u))).1
  change DerivedCategory.Q.map (T.map u) ≫
      ((inv (DerivedCategory.Q.map (T.map u)) ≫
        DerivedCategory.Q.map (T.map z)) ≫ DerivedCategory.Q.map (T.map b)) = _
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply DerivedCategory.Q_map_eq_of_homotopy
  apply F.mapHomotopy
  simpa only [u, z, Category.assoc] using hhom.symm.compLeft q

/-- Scalar extension of a K-flat augmented ordered localization model is the tensor Cech
complex of the corresponding global list. This comparison does not involve a functorial
family, its transition maps, or the Godement construction (Stacks, Tags 0996, 099D and 099E). -/
theorem ringFamilyGlobalExtension_cech
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{wA} (RingSiteModules (ringFamilyGlobalRing O))]
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ)
    (εP : P ⟶ ringComplexSingle (ringFamilyGlobalRing O))
    (hflat : P.IsKFlatIndependentCoefficients)
    (hP : RingComplexHasCechModel (ringFamilyGlobalRing O)
      (ringFamilyGlobalIdeal O r f).val P εP) :
    ∃ e : DerivedCategory.Q.obj (ringedExtendedCech O r f).1 ≅
        DerivedCategory.Q.obj (ringFamilyGlobalExtensionComplex O P),
      e.hom ≫ DerivedCategory.Q.map (ringFamilyGlobalExtensionAugmentation O εP) =
        DerivedCategory.Q.map (ringedExtendedCech O r f).2 := by
  obtain ⟨K, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ :=
    hP r (ringFamilyGlobalList O r f) rfl
  have hK := ordered_coordinates_kflat (ringFamilyGlobalRing O) r
    (ringFamilyGlobalList O r f) K e₀ e hneg
  obtain ⟨c, hc⟩ :=
    ringFamilyGlobalExtension_ordered_iso O r f K a e₀ e l hneg hd₀ hd ha
  have hres : ∀ Z : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ,
      ∃ (W : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ)
        (q : W ⟶ Z), W.IsKFlatIndependentCoefficients ∧ QuasiIso q := by
    intro Z
    obtain ⟨W, q, hW, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)) Z
    exact ⟨W, q, hW, hq⟩
  obtain ⟨d, hd⟩ := augmented_iso_of_good_quasiIso (ringFamilyGlobalExtension O)
    CochainComplex.IsKFlatIndependentCoefficients hres
    (fun t ht ht' hq ↦ ringFamilyGlobalExtension_quasiIso_of_kflat O t ht ht' hq)
    K P (ringComplexSingle (ringFamilyGlobalRing O)) a εP hK hflat α hα
  let v := ((HomologicalComplex.singleMapHomologicalComplex (ringFamilyGlobalExtension O)
    (.up ℤ) 0).app (ringComplexUnit (ringFamilyGlobalRing O))).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (ringFamilyGlobalExtensionUnit O)
  have hd' : d.hom ≫ DerivedCategory.Q.map (ringFamilyGlobalExtensionAugmentation O εP) =
      DerivedCategory.Q.map (ringFamilyGlobalExtensionAugmentation O a) := by
    have h := congrArg (fun t ↦ t ≫ DerivedCategory.Q.map v) hd
    simpa only [v, ringFamilyGlobalExtensionAugmentation, Functor.map_comp,
      Category.assoc] using h
  refine ⟨DerivedCategory.Q.mapIso c ≪≫ d, ?_⟩
  change (DerivedCategory.Q.map c.hom ≫ d.hom) ≫ _ = _
  rw [Category.assoc, hd', ← Functor.map_comp, hc]

end CategoryTheory
