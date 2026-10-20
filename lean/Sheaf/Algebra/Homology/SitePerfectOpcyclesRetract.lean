/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Local shortening of finite-projective complexes -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w' u' v' r m
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite
namespace SheafOfModules


private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e


private theorem flat_over_ofUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
    (hM : IsFlatOnSite (J := J) (R := R) M) (U : C) :
    IsFlatOnSite (J := J.over U) (R := R.over U) (M.over U) := by
  apply (isFlatOnSite_iff_local_equationalCriterion (R.over U) (M.over U)).2
  intro X n a s hs
  obtain ⟨S, hS, h⟩ :=
    (isFlatOnSite_iff_local_equationalCriterion R M).1 hM X.left n a s hs
  refine ⟨(Sieve.overEquiv X).symm S, ?_, ?_⟩
  · exact (J.mem_over_iff _).2 (by simpa using hS)
  · intro Y f hf
    exact h Y.left f.left hf

private theorem flat_iff_tensorLeft_preservesFiniteLimits
    {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] (X : A) :
    ObjectProperty.flat X ↔ PreservesFiniteLimits (tensorLeft X) := by
  refine ⟨fun h ↦ h.1.1, fun h ↦ ⟨⟨h,
    (inferInstance : PreservesFiniteColimits (tensorLeft X))⟩, ?_, ?_⟩⟩
  · exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  · exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

-- The Tor diagram chase of FlatModel.flat_opcycles_of_exactAt uses only right exactness
-- of tensor, supplied here directly by colimit preservation instead of closedness.
private theorem flat_opcycles_of_tensor_exactAt
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalPreadditive A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    (P : CochainComplex A ℤ) (a : ℤ)
    (h₁ : ObjectProperty.flat (P.X (a - 1))) (h₂ : ObjectProperty.flat (P.X a))
    (hP : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    ObjectProperty.flat (P.opcycles a) := by
  have := h₁.tensorLeft.preservesFiniteLimits
  have := h₂.tensorLeft.preservesFiniteLimits
  rw [flat_iff_tensorLeft_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  dsimp
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : A) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  -- the cokernel sequence `P^{a-1} ⟶ P^a ⟶ C ⟶ 0`, tensored with any object, stays exact
  have hcok (F : A) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : A) : Epi (p ▷ F) := (tensorRight F).map_epi p
  have hge (X : A) : Epi (X ◁ S.g) := (tensorLeft X).map_epi S.g
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `P^a ⊗ S.X₁`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  -- its image in `P^a ⊗ S.X₂` dies in `C ⊗ S.X₂`, so it comes from `P^{a-1} ⊗ S.X₂`
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  -- the image of `z` in `P^{a-1} ⊗ S.X₃` is a cycle, hence a boundary
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 (hP S.X₃)
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  -- correcting `z` by a boundary, it comes from `P^{a-1} ⊗ S.X₁`
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

set_option synthInstance.maxSize 512 in
private theorem tor_restrict_ofUniverses
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    [hDU : ∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (E : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (U : C) (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ (G : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((wfSiteDerivedTensor J R).obj
          (E, (DerivedCategory.singleFunctor _ 0).obj G)))) :
    let : HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (R.over U))) := hDU U
    ∀ (G : SheafOfModules.{max u v}
        (((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((wfSiteDerivedTensor (J.over U) (R.over U)).obj
          (ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose J
              (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U E,
            (DerivedCategory.singleFunctor _ 0).obj G))) := by
  classical
  let : HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (R.over U))) := hDU U
  let O := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let F := overFunctor.{max u v} O U
  have : PreservesFiniteLimits F := (overFunctor_exact_ofUniverses O U).1
  have : PreservesFiniteColimits F := (overFunctor_exact_ofUniverses O U).2
  obtain ⟨B, hflat, hbound, ⟨e⟩⟩ :=
    (torAmplitude_iff_exists_bounded_flat_model J R E a b hab).1 hTor
  apply (torAmplitude_iff_exists_bounded_flat_model
    (J.over U) (R.over U) _ a b hab).2
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj B, ?_, ?_, ?_⟩
  · intro i
    exact flat_over_ofUniverses R (B.X i) (hflat i) U
  · intro i hi
    exact F.map_isZero (hbound i hi)
  · exact ⟨overFunctor_derivedRestrictionIso O U E ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app B⟩

private theorem pushforward_finiteLimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [G.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesFiniteLimits (pushforward.{m} φ) := by
  let T := forget.{m} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (pushforward.{m} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((forget.{m} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem pushforward_colimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {G : C ⥤ D} [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{m}), G.op.HasPointwiseRightKanExtension F]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesColimitsOfSize.{m, m} (pushforward.{m} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{m} J K
  have : PreservesColimitsOfSize.{m, m} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{m} J K).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{m, m} (toSheaf.{m} R) :=
    ⟨fun {I} _ ↦ ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 I).2.1⟩
  let T := toSheaf.{m} S
  have : PreservesColimitsOfSize.{m, m} (pushforward.{m} φ ⋙ T) := by
    change PreservesColimitsOfSize.{m, m} (toSheaf.{m} R ⋙ H)
    infer_instance
  have : ReflectsColimitsOfSize.{m, m} T :=
    ⟨fun {_} _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  exact preservesColimits_of_reflects_of_preserves (pushforward.{m} φ) T

private theorem over_preserves_colimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    PreservesColimitsOfSize.{max u v, max u v} (overFunctor.{max u v} R U) := by
  exact pushforward_colimits (𝟙 _)

private theorem finite_presentation_global
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (M : SheafOfModules.{max u v} R)
    (P : M.Presentation) [P.IsFinite] : M.IsFinitePresentation := by
  have (U : C) := over_preserves_colimits R U
  let D : M.QuasicoherentData :=
    { I := C
      X := id
      coversTop := fun X ↦ J.superset_covering (by intro Y f _; exact ⟨X, ⟨f⟩⟩)
        (J.top_mem X)
      presentation U := P.map (overFunctor R U) (Iso.refl _) }
  have : D.IsFinitePresentation := ⟨fun U ↦ Presentation.isFinite_map _ _ _⟩
  exact D.isFinitePresentation

private noncomputable def freePowerIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ unit R) ≅ free (R := R) (ULift.{max u v} (Fin n)) := by
  let : HasFiniteBiproducts (SheafOfModules.{max u v} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  change (∏ᶜ fun _ : Fin n ↦ unit R) ≅
    (∐ fun _ : ULift.{max u v} (Fin n) ↦ unit R)
  exact (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv (f := fun _ : Fin n ↦ unit R)
      (g := fun _ : ULift.{max u v} (Fin n) ↦ unit R) Equiv.ulift.symm
      (fun _ ↦ Iso.refl _)

private theorem finite_presentation_cokernel_retract
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    {A B Q : SheafOfModules.{max u v} R} (d : A ⟶ B) (q : B ⟶ Q)
    (hdq : d ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q hdq))
    (r s : ℕ) (hr : Retract A (∏ᶜ fun _ : Fin r ↦ unit R))
    (hs : Retract B (∏ᶜ fun _ : Fin s ↦ unit R)) :
    ∃ D : Q.Presentation, D.IsFinite := by
  classical
  let e₁ := freePowerIso R r
  let e₂ := freePowerIso R s
  let iA := hr.i ≫ e₁.hom
  let pA := e₁.inv ≫ hr.r
  let iB := hs.i ≫ e₂.hom
  let pB := e₂.inv ≫ hs.r
  have hA : iA ≫ pA = 𝟙 A := by simp [iA, pA, hr.retract]
  have hB : iB ≫ pB = 𝟙 B := by simp [iB, pB, hs.retract]
  let c := coprod.desc (𝟙 _ - pB ≫ iB) (pA ≫ d ≫ iB)
  let p := pB ≫ q
  have hcp : c ≫ p = 0 := by
    apply coprod.hom_ext
    · simp only [c, p, coprod.inl_desc_assoc, Preadditive.sub_comp,
        Category.id_comp, Category.assoc, reassoc_of% hB, sub_self, comp_zero]
    · simp only [c, p, coprod.inr_desc_assoc, Category.assoc, reassoc_of% hB,
        hdq, comp_zero]
  have : Epi q := epi_of_isColimit_cofork hq
  have : Epi pB := epi_of_epi_fac hB
  have : Epi p := inferInstanceAs (Epi (pB ≫ q))
  let hcol : IsColimit (CokernelCofork.ofπ p hcp) :=
    CokernelCofork.IsColimit.ofπ' p hcp (by
      intro T k hk
      have h₁ : (𝟙 _ - pB ≫ iB) ≫ k = 0 := by
        simpa [c] using congrArg (fun z ↦ coprod.inl ≫ z) hk
      have h₂ : (pA ≫ d ≫ iB) ≫ k = 0 := by
        simpa [c] using congrArg (fun z ↦ coprod.inr ≫ z) hk
      have h₃ : pB ≫ iB ≫ k = k :=
        (sub_eq_zero.mp (by simpa only [Preadditive.sub_comp, Category.id_comp,
          Category.assoc] using h₁)).symm
      have h₄ : d ≫ iB ≫ k = 0 := by
        calc
          d ≫ iB ≫ k = (iA ≫ pA) ≫ d ≫ iB ≫ k := by rw [hA, Category.id_comp]
          _ = iA ≫ ((pA ≫ d ≫ iB) ≫ k) := by simp only [Category.assoc]
          _ = 0 := by rw [h₂, comp_zero]
      refine ⟨hq.desc (CokernelCofork.ofπ (iB ≫ k) h₄), ?_⟩
      dsimp [p]
      have hf : q ≫ hq.desc (CokernelCofork.ofπ (iB ≫ k) h₄) = iB ≫ k :=
        hq.fac _ WalkingParallelPair.one
      rw [Category.assoc, hf]
      exact h₃)
  let e := freeSumIso (R := R) (ULift.{max u v} (Fin s)) (ULift.{max u v} (Fin r))
  let f := e.inv ≫ c
  have hf : f ≫ p = 0 := by simp [f, Category.assoc, hcp]
  let hcol' : IsColimit (CokernelCofork.ofπ p hf) :=
    isCokernelEpiComp hcol e.inv rfl
  refine ⟨presentationOfIsCokernelFree f p hf hcol', ?_⟩
  exact ⟨⟨inferInstanceAs (Finite (ULift.{max u v} (Fin s)))⟩,
    ⟨inferInstanceAs (Finite (ULift.{max u v} (Fin s) ⊕ ULift.{max u v} (Fin r)))⟩⟩

/-- A retract on the terminal object of the localized slice transports to the corresponding
retract after restriction along its underlying arrow. This is the iterated-slice comparison
for `overMap`; it is the final relocalization step in Tags 08G7 and 04IX.

Proof: push the displayed retraction along the inverse of the iterated-slice equivalence.
This restriction preserves finite limits, hence finite products, and sends the unit to
the unit. Identify its application to the restricted module with direct `overMap` by
the defining equality of the underlying functors. Conjugating the mapped splitting
by these two comparisons proves the assertion.

Source: Stacks Project, Cohomology on Sites, Tags 08G7 and 04IX.
(blueprint: lem-sf-site-perfect-opcycles-retract-transport). -/
theorem transport_slice_retract
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{max u v}) (U V : C) (f : V ⟶ U)
    (M : SheafOfModules.{max u v} (O.over U)) (n : ℕ)
    (h : Nonempty (Retract (M.over (Over.mk f))
      (∏ᶜ fun _ : Fin n ↦ unit ((O.over U).over (Over.mk f))))) :
    Nonempty (Retract ((overMap O f).obj M)
      (∏ᶜ fun _ : Fin n ↦ unit (O.over V))) := by
  let X : Over U := Over.mk f
  let H : SheafOfModules.{max u v} ((O.over U).over X) ⥤
      SheafOfModules.{max u v} (O.over X.left) :=
    pushforward (F := X.iteratedSliceBackward) (𝟙 _)
  have : PreservesFiniteLimits H := pushforward_finiteLimits (𝟙 _)
  let eU : H.obj (unit ((O.over U).over X)) ≅ unit (O.over X.left) := Iso.refl _
  let e := PreservesProduct.iso H (fun _ : Fin n ↦ unit ((O.over U).over X)) ≪≫
    Pi.mapIso (fun _ : Fin n ↦ eU)
  let eN : H.obj (M.over X) ≅ (overMap.{max u v} O f).obj M := Iso.refl _
  obtain ⟨r⟩ := h
  refine ⟨⟨eN.inv ≫ H.map r.i ≫ e.hom, e.inv ≫ H.map r.r ≫ eN.hom, ?_⟩⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (H.map r.i), ← H.map_comp, r.retract, H.map_id,
    Category.id_comp, Iso.inv_hom_id]

/-- The bottom opcycle of a bounded finite-free-retract model is locally a finite
free retract when its represented object has Tor amplitude in `[a,b]`.

Source: Stacks Project, Cohomology on Sites, Tag 08G7 (lemma-perfect-precise),
last cokernel and finite-presentation argument, using Tags 08G0 and 08FD.

Proof: Restrict the universal Tor condition using the bounded flat model and
the local equational criterion for flatness. Each term of P is flat, since tensor by a finite-free
retract is a retract of a finite sum of the identity. The bounded complex is
K-flat. The first-variable derived-tensor comparison and the degree-zero tensor
isomorphism identify ordinary tensor by P with derived tensor. Hence it is exact
in degree a-1 for every test module. The opcycle Tor
criterion makes P.opcycles a flat. It is finitely presented: write splittings
P^a → O^s → P^a and P^(a-1) → O^r → P^(a-1), and present the opcycle as the
cokernel of (1-ip, i d q): O^s ⊕ O^r → O^s. The relations identify precisely
the kernel of the map O^s → P^a → P.opcycles a; these are sheaf cokernels,
not cokernels of global sections. Apply the flat finitely presented finite-free
retract theorem to this opcycle. The slice covering at the terminal slice
object is exactly a covering of U. Relocalization identifies its restricted
opcycle with the displayed overMap object. Rank zero, empty coverings and
zero rings satisfy the same universal-property calculations.
(blueprint: lem-sf-site-perfect-opcycles-retract). -/
theorem exists_local_retract_opcycles_of_perfect_tor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    [hDU : ∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (E : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (U : C)
    (P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R U
      (ringedSiteDerivedRestrictionOfUniverses
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U E))
    (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ (G : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((wfSiteDerivedTensor J R).obj
          (E, (DerivedCategory.singleFunctor _ 0).obj G)))) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ n : ℕ, Nonempty (Retract
          ((overMap.{max u v}
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
            f).obj (P.F.opcycles a))
          (∏ᶜ fun _ : Fin n ↦ unit
            (((sheafCompose J
              (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over V))) := by
  classical
  let O := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let RU := R.over U
  let : HasDerivedCategory.{w'} (SheafOfModules.{max u v} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU)) := hDU U
  let := isMonoidal_W_independentCoefficients RU
  let := monoidalCategory RU
  let := symmetricCategory RU
  let := tensorPreadditive RU
  let A : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU)) ℤ := P.F
  let : HasFiniteBiproducts (SheafOfModules.{max u v} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hflat (n : ℤ) : IsFlatOnSite (J := J.over U) (R := RU) (A.X n) := by
    have hd : IsDualizable (A.X n) :=
      IsDualizable.of_retract ⟨P.package.i n, P.package.p n, P.package.splitting n⟩
        (isDualizable_finite_power _ isDualizable_unit (P.package.N n))
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso RU (A.X n)).symm hd.flat.2
  obtain ⟨l, t, hbound⟩ := P.bounded
  have : A.IsStrictlyLE t := (CochainComplex.isStrictlyLE_iff A t).2
    (fun n hn ↦ hbound n (Or.inr hn))
  have hk : CochainComplex.IsAcyclicTensorKFlat (J := J.over U) (R := RU) A :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (J := J.over U) (R := RU) A).1
      (isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite RU A t hflat)
  have hex (N : SheafOfModules.{max u v} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU)) :
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj A).ExactAt (a - 1) := by
    obtain ⟨e⟩ := wfSiteDerivedTensor_first (J.over U) RU A
      ((CochainComplex.singleFunctor _ 0).obj N) hk
      (fun n ↦ (flat_to_cat RU _ (hflat n)).2)
    let eN := (DerivedCategory.singleFunctorIsoCompQ _ 0).app N
    let eD := (wfSiteDerivedTensor (J.over U) RU).mapIso
      (Iso.prod P.represents.symm eN.symm)
    have hz := tor_restrict_ofUniverses J R E U a b hab hTor N (a - 1)
      (Or.inl (by omega))
    have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ (a - 1)).mapIso
      (e ≪≫ eD))
    have hh : IsZero ((CochainComplex.mapBifunctor A
        ((CochainComplex.singleFunctor _ 0).obj N) (curriedTensor _)).homology (a - 1)) :=
      hz'.of_iso ((DerivedCategory.homologyFunctorFactors _ (a - 1)).app _).symm
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hh).of_iso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N A)
  have (N : SheafOfModules.{max u v} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU)) :
      PreservesColimitsOfSize.{0, 0} (tensorLeft N) := by
    have := tensorLeft_preservesColimits_independentCoefficients RU N
    exact preservesColimitsOfSize_shrink (tensorLeft N)
  have hop : IsFlatOnSite (J := J.over U) (R := RU) (A.opcycles a) := by
    have hc := flat_opcycles_of_tensor_exactAt A a
      (flat_to_cat RU _ (hflat _)) (flat_to_cat RU _ (hflat _)) hex
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso RU (A.opcycles a)).symm hc.2
  let O' := (sheafCompose (J.over U)
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj RU
  let (X : Over U) : HasSheafify ((J.over U).over X) AddCommGrpCat.{max u v} :=
    X.iteratedSliceEquiv.hasSheafify ((J.over U).over X) (J.over X.left)
      AddCommGrpCat.{max u v}
  let (X : Over U) : ((J.over U).over X).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.transport
      ((J.over U).over X) (J.over X.left) X.iteratedSliceEquiv.inverse
      (Functor.IsDenseSubsite.coverPreserving (J.over X.left) ((J.over U).over X)
        X.iteratedSliceEquiv.inverse)
  obtain ⟨D, hD⟩ := finite_presentation_cokernel_retract O'
    (A.d (a - 1) a) (A.pOpcycles a) (A.d_pOpcycles _ _)
    (A.opcyclesIsCokernel (a - 1) a (by simp))
    (P.package.N (a - 1)) (P.package.N a)
    ⟨P.package.i _, P.package.p _, P.package.splitting _⟩
    ⟨P.package.i _, P.package.p _, P.package.splitting _⟩
  have hfp : (A.opcycles a).IsFinitePresentation := finite_presentation_global O' _ D
  obtain ⟨S, hS, h⟩ := exists_local_finiteFree_retract_of_flat_of_finitePresentation
    RU (A.opcycles a) hop hfp (Over.mk (𝟙 U))
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 U)) S, hS, ?_⟩
  intro V f hf
  obtain ⟨n, i, p, hip⟩ := h _ _ ((Sieve.overEquiv_iff _ _).1 hf)
  refine ⟨n, ?_⟩
  have ht := transport_slice_retract O U V (f ≫ 𝟙 U) (A.opcycles a) n ⟨⟨i, p, hip⟩⟩
  simpa only [Category.comp_id] using ht

end SheafOfModules
