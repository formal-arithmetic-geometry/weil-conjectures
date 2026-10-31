/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectReductionCoefficientUnits
import WeilConjectures.Algebra.Homology.ExtensionTensorComparisonIndependent
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # The normalized principal Koszul tensor augmentation

Source: Bhatt--Scholze, Lemma 3.5.5, the perfect-complex comparison.
(blueprint: lem-sp-perfect-reduction-koszul-comparison-alpha-data).

We identify the sheafified principal quotient as a module cokernel, augment the
principal Koszul complex to that quotient, and tensor with the given K-flat complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
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
structure KoszulAlphaData
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) where
  α : ∀ m, (total R).obj (principalKoszul R t m) ⟶
    (d m).E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  α_zero : ∀ m Z i p n (h : p + i = n), p ≠ 0 →
      ι R (principalKoszul R t m) Z p i n h ≫ ((α m).app Z).f n = 0
  α_unit : ∀ m Z n,
      ((tensor R).map (koszulZeroInclusion R t m)).app (Z.X n) ≫
        ι R (principalKoszul R t m) Z 0 n n (zero_add n) ≫ ((α m).app Z).f n =
          ((SheafOfModules.monoidalCategory R).leftUnitor (Z.X n)).hom ≫
            ((c.ρ m).app Z).f n
  α_quasiIso : ∀ m Z,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) Z → QuasiIso ((α m).app Z)
attribute [local semireducible] principalPowerRingQuotient

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r} (forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

private def quotientModulePresheaf (m : ℕ) :
    PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R).obj :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight (sectionPowerQuotientProjection R (ringSection R t) (m + 1))
      (forget₂ CommRingCat RingCat))).obj
    (PresheafOfModules.unit
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1) ⋙
        forget₂ CommRingCat RingCat))

private def quotientModuleUnit (m : ℕ) : quotientModulePresheaf R t m ⟶
    ((restriction (powerProjection R t m)).obj
      (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m)))).val :=
  PresheafOfModules.homMk
    (Functor.whiskerRight
      (toSheafify J (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1)))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
      intro U a x
      change (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1)).obj U at x
      change (toSheafify J
        (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
        ((sectionPowerQuotientProjection R (ringSection R t) (m + 1)).app U a * x) = _
      exact map_mul _ _ _)

private def quotientModuleProjection (m : ℕ) :
    (unit (derivedChangeRingIndependentCoefficients J R)).val ⟶
      quotientModulePresheaf R t m :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (sectionPowerQuotientProjection R (ringSection R t) (m + 1))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
      intro U a x
      exact map_mul (Ideal.Quotient.mk _) _ _)

private lemma quotientModule_factor (m : ℕ) :
    quotientModuleProjection R t m ≫ quotientModuleUnit R t m =
      (ringMap (powerProjection R t m)).val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (toSheafify J
    (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) x) =
        ((powerProjection R t m).hom.app U).hom x *
          (1 : (powerRing R t m).obj.obj U)
  rw [mul_one]
  rfl

private instance quotientModuleUnit_surjective (m : ℕ) :
    PresheafOfModules.IsLocallySurjective J (quotientModuleUnit R t m) where
  imageSieve_mem x := Presheaf.imageSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))) x

private instance quotientModuleUnit_injective (m : ℕ) :
    PresheafOfModules.IsLocallyInjective J (quotientModuleUnit R t m) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))) x y h

private theorem scalarPower_unit (n : ℕ) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (endoPow (globalSectionMultiplication R t) n).val.app U x =
      x * (@id (R.obj.obj U) (t.val U)) ^ n := by
  induction n with
  | zero => change x = _; simp
  | succ n ih =>
    change (@id (R.obj.obj U)
      ((endoPow (globalSectionMultiplication R t) n).val.app U x)) *
        (@id (R.obj.obj U) (t.val U)) = _
    rw [ih, pow_succ]
    exact mul_assoc _ _ _

private theorem quotient_scalar_zero (m : ℕ) :
    endoPow (globalSectionMultiplication R t) (m + 1) ≫
      ringMap (powerProjection R t m) = 0 := by
  have hz (U : Cᵒᵖ) : ((powerProjection R t m).hom.app U).hom
      ((@id (R.obj.obj U) (t.val U)) ^ (m + 1)) = 0 := by
    unfold powerProjection principalPowerRingProjection principalPowerRingQuotient
    change ((toSheafify J
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U).hom
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) _) = 0
    have h : Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U)
        ((@id (R.obj.obj U) (t.val U)) ^ (m + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    erw [h]
    exact map_zero _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((powerProjection R t m).hom.app U).hom
    ((endoPow (globalSectionMultiplication R t) (m + 1)).val.app U x) * 1 = 0
  rw [scalarPower_unit, map_mul, hz, mul_zero, mul_one]

private theorem quotient_module_lift (m : ℕ) (N : RegularQuotientCone.Modules R)
    (f : unit (derivedChangeRingIndependentCoefficients J R) ⟶ N)
    (hf : endoPow (globalSectionMultiplication R t) (m + 1) ≫ f = 0) :
    ∃! l : (restriction (powerProjection R t m)).obj
        (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))) ⟶ N,
      ringMap (powerProjection R t m) ≫ l = f := by
  have hzero (U : Cᵒᵖ) (x : R.obj.obj U)
      (hx : x ∈ sectionPowerIdeal R (ringSection R t) (m + 1) U) :
      f.val.app U x = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    have h := congrArg (fun k ↦ k.val.app U y) hf
    change f.val.app U ((endoPow (globalSectionMultiplication R t) (m + 1)).val.app U y)
      = 0 at h
    rw [scalarPower_unit] at h
    change x = (@id (R.obj.obj U) (t.val U)) ^ (m + 1) * y at hy
    rw [hy, mul_comm] at ⊢
    exact h
  let ψapp (U : Cᵒᵖ) :
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1)).obj U →+ N.val.obj U :=
    QuotientAddGroup.lift (sectionPowerIdeal R (ringSection R t) (m + 1) U).toAddSubgroup
      (f.val.app U).hom.toAddMonoidHom (hzero U)
  let ψ : quotientModulePresheaf R t m ⟶ N.val :=
    PresheafOfModules.homMk
      { app := fun U ↦ AddCommGrpCat.ofHom (ψapp U)
        naturality := by
          intro U V g
          ext x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact PresheafOfModules.naturality_apply f.val g x }
      (by
        intro U a x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (f.val.app U).hom.map_smul a x)
  have hp : quotientModuleProjection R t m ≫ ψ = f.val := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  let e := PresheafOfModules.homEquivOfIsLocallyBijective
    (quotientModuleUnit R t m) N.isSheaf
  let l : (restriction (powerProjection R t m)).obj
      (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))) ⟶ N :=
    ⟨e.symm ψ⟩
  have hl : ringMap (powerProjection R t m) ≫ l = f := by
    apply SheafOfModules.hom_ext
    rw [SheafOfModules.comp_val, ← quotientModule_factor R t m, Category.assoc]
    exact congrArg (fun k ↦ quotientModuleProjection R t m ≫ k) (e.apply_symm_apply ψ)
      |>.trans hp
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply SheafOfModules.hom_ext
  apply e.injective
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := congrArg (fun k ↦ k.val.app U x) (hk.trans hl.symm)
  change k.val.app U (((powerProjection R t m).hom.app U).hom x * 1) =
    l.val.app U (((powerProjection R t m).hom.app U).hom x * 1) at h
  change k.val.app U ((toSheafify J
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) x)) =
    l.val.app U ((toSheafify J
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) x))
  unfold powerProjection principalPowerRingProjection at h
  rw [mul_one] at h
  change k.val.app U ((toSheafify J
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) x)) =
    l.val.app U ((toSheafify J
      (sectionPowerQuotientPresheaf R (ringSection R t) (m + 1))).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R (ringSection R t) (m + 1) U) x)) at h
  exact h

private theorem quotient_shortExact (ht : Mono (globalSectionMultiplication R t)) (m : ℕ) :
    (ShortComplex.mk (endoPow (globalSectionMultiplication R t) (m + 1))
      (ringMap (powerProjection R t m)) (quotient_scalar_zero R t m)).ShortExact := by
  let := ht
  have hmono (n : ℕ) : Mono (endoPow (globalSectionMultiplication R t) n) := by
    induction n with
    | zero => dsimp [endoPow]; infer_instance
    | succ n ih => let := ih; dsimp [endoPow]; infer_instance
  let := hmono (m + 1)
  let hQ := CokernelCofork.IsColimit.ofπ
    (ringMap (powerProjection R t m)) (quotient_scalar_zero R t m)
    (fun f hf ↦ (quotient_module_lift R t m _ f hf).choose)
    (fun f hf ↦ (quotient_module_lift R t m _ f hf).choose_spec.1)
    (fun f hf k hk ↦ (quotient_module_lift R t m _ f hf).choose_spec.2 k hk)
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ hQ
          mono_f := hmono (m + 1)
          epi_g := epi_of_isColimit_cofork hQ }

open CategoryTheory.MonoidalCategory
open SheafOfModules.IndependentExtensionTensor
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
  tensorLeft_additive_independent

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem tensor_hom_ext (R : Sheaf J CommRingCat.{r})
    (M N H : RegularQuotientCone.Modules R) {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ V x y, f.val.app V ((tensorPresheafUnit M N).app V
        (x ⊗ₜ[R.obj.obj V] y)) =
      g.val.app V ((tensorPresheafUnit M N).app V (x ⊗ₜ[R.obj.obj V] y))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

private def pure (R : Sheaf J CommRingCat.{r}) (M N : RegularQuotientCone.Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :=
  (tensorPresheafUnit M N).app V (x ⊗ₜ[R.obj.obj V] y)

private theorem tensor_map_tmul (A : Sheaf J CommRingCat.{r})
    {M M' N N' : RegularQuotientCone.Modules A} (f : M ⟶ M') (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorHom f g).val.app V (pure A M N V x y) =
      pure A M' N' V (f.val.app V x) (g.val.app V y) := by
  let := monoidalCategory A
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  have ht : (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) := by
    let sh := PresheafOfModules.sheafification (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
    let ε := asIso adj.counit
    have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ sh.map f.val :=
      ε.inv.naturality f
    have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ sh.map g.val :=
      ε.inv.naturality g
    change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
        Functor.LaxMonoidal.μ sh M'.val N'.val =
      ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
        Functor.LaxMonoidal.μ sh M.val N.val ≫ sh.map (f.val ⊗ₘ g.val)
    rw [← Functor.LaxMonoidal.μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]
  have hi : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun h ↦ h.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))) hi
  have hη := congrArg (fun h ↦ h.app V (x ⊗ₜ[A.obj.obj V] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  exact hh.trans (congrArg ((tensorObjIsoSheafification M' N').inv.val.app V) hη.symm)


private def tensorModelIso (m : ℕ)
    (D : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (M : RegularQuotientCone.Modules R) :
    (monoidalCategory R).tensorObj
      ((restriction (powerProjection R t m)).obj
        (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m)))) M ≅
      (restriction (powerProjection R t m)).obj (D.E.obj M) :=
  (exists_extensionTensorComparison (powerProjection R t m) M).choose ≪≫
    (restriction (powerProjection R t m)).mapIso (eqToIso (D.obj_eq M).symm)

private theorem tensorModelIso_tmul (m : ℕ)
    (D : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (M : RegularQuotientCone.Modules R) (U : Cᵒᵖ)
    (s : (powerRing R t m).obj.obj U) (x : M.val.obj U) :
    (tensorModelIso R t m D M).hom.val.app U
      ((tensorPresheafUnit
        ((restriction (powerProjection R t m)).obj
          (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))))
        M).app U (s ⊗ₜ[R.obj.obj U] x)) =
      s • (eqToHom (D.obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (powerProjection R t m) M).presheaf).app U
          ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
            ((powerProjection R t m).hom.app U).hom] x)) := by
  change (eqToHom (D.obj_eq M).symm).val.app U
      (((exists_extensionTensorComparison (powerProjection R t m) M).choose).hom.val.app U _)
      = _
  rw [(exists_extensionTensorComparison (powerProjection R t m) M).choose_spec]
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J (powerRing R t m)).obj)).unit.app
      (changeOfRingsPresheaf (powerProjection R t m) M)
  change (eqToHom (D.obj_eq M).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, ((powerProjection R t m).hom.app U).hom] x)) =
    s • (eqToHom (D.obj_eq M).symm).val.app U
      (η.app U ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
        ((powerProjection R t m).hom.app U).hom] x))
  erw [← ((eqToHom (D.obj_eq M).symm).val.app U).hom.map_smul,
    ← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[R.obj.obj U, ((powerProjection R t m).hom.app U).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj U, ((powerProjection R t m).hom.app U).hom] x
  rw [mul_one]

private def tensorModelNatIso (m : ℕ)
    (D : DerivedChangeOfRingsCochainModel (powerProjection R t m)) :
    (tensor R).obj
        ((restriction (powerProjection R t m)).obj
          (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m)))) ≅
      D.E ⋙ restriction (powerProjection R t m) :=
  NatIso.ofComponents (tensorModelIso R t m D) (by
    intro M N f
    obtain ⟨_, _, ho⟩ := sheafRingCoefficientOrdinaryAdjunction (powerProjection R t m)
    obtain ⟨adj, ha⟩ := ho D.E D.obj_eq D.map_eq
    have hu (M : RegularQuotientCone.Modules R) (U : Cᵒᵖ) (x : M.val.obj U) :
        (eqToHom (D.obj_eq M).symm).val.app U
          ((toSheafify J (changeOfRingsPresheaf (powerProjection R t m) M).presheaf).app U
            ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
              ((powerProjection R t m).hom.app U).hom] x)) =
          (adj.unit.app M).val.app U x := by
      have h := ha M (D.E.obj M) (eqToHom (D.obj_eq M).symm) U x
      simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
      exact h.symm
    change (_ ◁ f) ≫ (tensorModelIso R t m D N).hom =
      (tensorModelIso R t m D M).hom ≫ (restriction _).map (D.E.map f)
    rw [← id_tensorHom]
    apply tensor_hom_ext R
    intro U s x
    have hf := tensor_map_tmul R (𝟙 _) f U s x
    change (tensorModelIso R t m D N).hom.val.app U
        ((𝟙 _ ⊗ₘ f).val.app U (pure R _ M U s x)) =
      (D.E.map f).val.app U
        ((tensorModelIso R t m D M).hom.val.app U (pure R _ M U s x))
    rw [hf]
    change (tensorModelIso R t m D N).hom.val.app U
        ((tensorPresheafUnit _ N).app U (s ⊗ₜ[R.obj.obj U] (f.val.app U x))) =
      (D.E.map f).val.app U ((tensorModelIso R t m D M).hom.val.app U
        ((tensorPresheafUnit _ M).app U (s ⊗ₜ[R.obj.obj U] x)))
    rw [tensorModelIso_tmul, tensorModelIso_tmul, hu, hu]
    erw [map_smul]
    congr 1
    exact congrArg (fun k ↦ k.val.app U x) (adj.unit.naturality f))

private def tensorCoefficientIso (m : ℕ)
    (D : DerivedChangeOfRingsCochainModel (powerProjection R t m)) :
    (total R).obj ((CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).obj
        ((restriction (powerProjection R t m)).obj
          (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))))) ≅
      D.E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexObjSingleIso (tensor R) _ ≪≫
    NatIso.mapHomologicalComplex (tensorModelNatIso R t m D) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (D.E ⋙ restriction
      (powerProjection R t m))) (.up ℤ)).symm

attribute [local semireducible] SheafOfModules.monoidalCategory in
private theorem regularTensorIso_eq
    {A : Type*} [Category A] [EssentiallySmall.{u} A]
    {J : GrothendieckTopology A}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.IndependentExtensionTensor.regularTensorIso M = (λ_ M) := by
  apply Iso.ext
  dsimp only [SheafOfModules.IndependentExtensionTensor.regularTensorIso,
    SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_inv, Iso.app_inv, asIso_inv]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.map_leftUnitor,
    Category.assoc]
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
  change (e.app (SheafOfModules.unit _) ⊗ᵢ e.app M).inv ≫
    Functor.LaxMonoidal.μ F (𝟙_ _) M.val ≫
    Functor.OplaxMonoidal.δ F (𝟙_ _) M.val ≫
    (SheafOfModules.sheafificationObjUnitIso R).hom ▷ F.obj M.val ≫
    (λ_ (F.obj M.val)).hom ≫ (e.app M).hom = _
  rw [Functor.Monoidal.μ_δ_assoc]
  simp only [SheafOfModules.sheafificationObjUnitIso, tensorIso_inv, tensorHom_def',
    Category.assoc, ← leftUnitor_naturality]
  change (𝟙_ _) ◁ (e.app M).inv ≫
    (e.app (SheafOfModules.unit _)).inv ▷ F.obj M.val ≫
    (e.app (SheafOfModules.unit _)).hom ▷ F.obj M.val ≫
    (𝟙_ _) ◁ (e.app M).hom ≫ (λ_ M).hom = _
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, ← whiskerLeft_comp_assoc, whiskerLeft_id]

attribute [local semireducible] SheafOfModules.monoidalCategory in
private theorem tensorModelIso_unit
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) (m : ℕ)
    (Z : CochainComplex (RegularQuotientCone.Modules R) ℤ) (n : ℤ) :
    ((tensor R).map (ringMap (powerProjection R t m))).app (Z.X n) ≫
        (tensorModelIso R t m (d m) (Z.X n)).hom =
      ((monoidalCategory R).leftUnitor (Z.X n)).hom ≫ ((c.ρ m).app Z).f n := by
  apply (cancel_epi ((monoidalCategory R).leftUnitor (Z.X n)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  rw [← regularTensorIso_eq R (Z.X n)]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (tensorModelIso R t m (d m) (Z.X n)).hom.val.app U
    ((ringMap (powerProjection R t m) ▷ Z.X n).val.app U
      ((regularTensorIso (Z.X n)).inv.val.app U x)) = _
  rw [regularTensorIso_inv_apply]
  erw [tensorPresheafUnit_whiskerRight_apply]
  have h1 : (ringMap (powerProjection R t m)).val.app U (1 : R.obj.obj U) =
      (1 : (powerRing R t m).obj.obj U) := by
    change ((powerProjection R t m).hom.app U).hom 1 * 1 = 1
    rw [map_one, one_mul]
  rw [h1, tensorModelIso_tmul, one_smul]
  have hc := (c.ρ_sections m Z n U x)
  change (eqToHom ((d m).obj_eq (Z.X n))).val.app U
    ((((c.ρ m).app Z).f n).val.app U x) =
      (toSheafify J (changeOfRingsPresheaf (powerProjection R t m) (Z.X n)).presheaf).app U
        ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
          ((powerProjection R t m).hom.app U).hom] x) at hc
  rw [← hc]
  change (((restriction (powerProjection R t m)).map
    (eqToHom ((d m).obj_eq (Z.X n))) ≫
      (restriction (powerProjection R t m)).map
        (eqToHom ((d m).obj_eq (Z.X n)).symm)).val.app U) _ = _
  simp only [← Functor.map_comp, eqToHom_trans, eqToHom_refl, Functor.map_id]
  rfl

private theorem tensorCoefficientIso_unit (m : ℕ)
    (D : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (Z : CochainComplex (RegularQuotientCone.Modules R) ℤ) (n : ℤ) :
    ((tensor R).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        ((restriction (powerProjection R t m)).obj
          (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))))).inv).app
        (Z.X n) ≫
      ι R ((CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).obj
        ((restriction (powerProjection R t m)).obj
          (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m)))))
        Z 0 n n (zero_add n) ≫
      ((tensorCoefficientIso R t m D).hom.app Z).f n =
        (tensorModelIso R t m D (Z.X n)).hom := by
  rw [← Category.assoc]
  change (CochainComplex.mapBifunctorSingle₁Iso (tensor R) _ Z).inv.f n ≫ _ = _
  dsimp only [tensorCoefficientIso, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f]
  simp only [CochainComplex.map₂HomologicalComplexObjSingleIso_hom_app]
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    Category.id_comp]
  rfl

private def quotientComplex (m : ℕ) :
    ShortComplex (CochainComplex (RegularQuotientCone.Modules R) ℤ) :=
  (ShortComplex.mk (endoPow (globalSectionMultiplication R t) (m + 1))
    (ringMap (powerProjection R t m)) (quotient_scalar_zero R t m)).map
      (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0)

private def quotientAugmentation (m : ℕ) : principalKoszul R t m ⟶
    (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).obj
      ((restriction (powerProjection R t m)).obj
        (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m)))) :=
  CochainComplex.mappingCone.descShortComplex (quotientComplex R t m)

private theorem quotientAugmentation_quasiIso
    (ht : Mono (globalSectionMultiplication R t)) (m : ℕ) :
    QuasiIso (quotientAugmentation R t m) := by
  have : PreservesFiniteLimits
      (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0) :=
    inferInstanceAs (PreservesFiniteLimits
      (HomologicalComplex.single (RegularQuotientCone.Modules R) (.up ℤ) 0))
  have : PreservesFiniteColimits
      (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0) :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (RegularQuotientCone.Modules R) (.up ℤ) 0))
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    ((quotient_shortExact R t ht m).map_of_exact
      (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0))

private theorem quotientAugmentation_zero (m : ℕ) (p : ℤ) (hp : p ≠ 0) :
    (quotientAugmentation R t m).f p = 0 :=
  (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_tgt _ _

private theorem quotientAugmentation_unit (m : ℕ) :
    koszulZeroInclusion R t m ≫ (quotientAugmentation R t m).f 0 =
      ringMap (powerProjection R t m) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restriction (powerProjection R t m)).obj
            (unit (derivedChangeRingIndependentCoefficients J (powerRing R t m))))).inv := by
  have h := CochainComplex.mappingCone.inr_f_descShortComplex_f (quotientComplex R t m) 0
  calc
    _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (unit (derivedChangeRingIndependentCoefficients J R))).inv ≫
        ((CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).map
          (ringMap (powerProjection R t m))).f 0 :=
      congrArg (fun k ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (unit (derivedChangeRingIndependentCoefficients J R))).inv ≫ k) h
    _ = _ := by
      dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      erw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]

attribute [local semireducible] SheafOfModules.monoidalCategory

/-- Augmentation and quasi-isomorphism data; source Bhatt--Scholze Lemma 3.5.5.

Proof:
1. Multiplication by t^(m+1) is monic. Its cokernel is the actual sheafified
principal-power quotient: a module map killing the power factors sectionwise through
quotient groups, then uniquely descends along the locally bijective sheafification unit.
2. The cone augmentation to the quotient concentrated in degree zero is therefore a
quasi-isomorphism, by the short exact sequence cone lemma.
3. The normalized extension-tensor comparison identifies the tensor of this quotient
with a complex Z with the specified ordinary coefficient model. Naturality follows on
pure tensors from the ordinary adjunction unit. Its value on 1 tensor x agrees with c.
4. Tensor the cone augmentation with Z and compose with this natural isomorphism.
Every nonzero first degree vanishes because the target quotient complex is concentrated
in degree zero. The zero-degree inclusion gives the left unitor followed by c. Finally,
K-flat tensor preservation applied to the cone augmentation proves the quasi-isomorphism.
(blueprint: lem-sp-perfect-reduction-koszul-comparison-alpha-data). -/
theorem nonempty_koszulAlphaData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) : Nonempty (KoszulAlphaData R t d c) := by
  classical
  let α (m : ℕ) := (total R).map (quotientAugmentation R t m) ≫
    (tensorCoefficientIso R t m (d m)).hom
  refine ⟨{ α := α, α_zero := ?_, α_unit := ?_, α_quasiIso := ?_ }⟩
  · intro m Z i p n h hp
    change ι R (principalKoszul R t m) Z p i n h ≫
      (HomologicalComplex.mapBifunctorMap (quotientAugmentation R t m) (𝟙 Z)
        (tensor R) (.up ℤ)).f n ≫
      ((tensorCoefficientIso R t m (d m)).hom.app Z).f n = 0
    dsimp only [ι]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc,
      quotientAugmentation_zero R t m p hp]
    simp
  · intro m Z n
    change ((tensor R).map (koszulZeroInclusion R t m)).app (Z.X n) ≫
      ι R (principalKoszul R t m) Z 0 n n (zero_add n) ≫
      (HomologicalComplex.mapBifunctorMap (quotientAugmentation R t m) (𝟙 Z)
        (tensor R) (.up ℤ)).f n ≫
      ((tensorCoefficientIso R t m (d m)).hom.app Z).f n = _
    dsimp only [ι]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp,
      quotientAugmentation_unit, Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    have hunit := tensorCoefficientIso_unit R t m (d m) Z n
    dsimp only [ι] at hunit
    erw [hunit, tensorModelIso_unit R t d c]
  · intro m Z hZ
    have hq := kFlatTensorPreservesQuasiIsoIndependentCoefficients R Z hZ
      (quotientAugmentation R t m) (quotientAugmentation_quasiIso R t ht m)
    change QuasiIso (((koszulTensorFunctor R Z).map (quotientAugmentation R t m)) ≫
      (tensorCoefficientIso R t m (d m)).hom.app Z)
    let := hq
    infer_instance
end CategoryTheory.PerfectReductionRoos
