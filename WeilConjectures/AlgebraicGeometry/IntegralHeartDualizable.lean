/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalModelData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.AlgebraicGeometry.IntegralHeartRealizationExact
import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalDualityDescent
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.RingTheory.DiscreteValuationRing.DerivedQuotientDuality
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Local duals of integral constructible sheaves

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-int-integral-heart/sk-lem-int-integral-heart-dualizable.md,
all assertions (blueprint: det-lem-int-integral-heart-dualizable).

The coefficient ring is the existing continuous condensed integer ring pulled back
from the point, rather than the discrete constant integer ring. Level zero of the
positive quotient tower is the residue module, namely the quotient by a uniformizer.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Elaborate the category-theoretic proofs sequentially to bound retained contexts.
set_option Elab.async false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

-- Keep the canonical localization choices abstract during proof elaboration.
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale

private theorem appendFourth {P Q R S : Prop} (h : P ∧ Q ∧ R) (hs : S) :
    P ∧ Q ∧ R ∧ S := ⟨h.1, h.2.1, h.2.2, hs⟩

private theorem shortExactDualizableTor
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj S.X₃) ∧
      DerivedCategory.torAmplitudeIn A (-1) 0
        ((DerivedCategory.singleFunctor A 0).obj S.X₃) := by
  refine ⟨DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS h₁ h₂, ?_⟩
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  let e := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₃).symm
  exact (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0
      (fun n ↦ (DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem transportSingleDualTor
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    (M N : A) (e : M ≅ N)
    (h : IsDualizable ((DerivedCategory.singleFunctor A 0).obj N) ∧
      DerivedCategory.torAmplitudeIn A (-1) 0 ((DerivedCategory.singleFunctor A 0).obj N)) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj M) ∧
      DerivedCategory.torAmplitudeIn A (-1) 0 ((DerivedCategory.singleFunctor A 0).obj M) := by
  let e' := (DerivedCategory.singleFunctor A 0).mapIso e
  exact ⟨h.1.of_iso e'.symm,
    (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e'.symm h.2⟩


private theorem unitQuotientDual
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {S : ShortComplex A} (hs : S.ShortExact)
    (e₁ : S.X₁ ≅ 𝟙_ A) (e₂ : S.X₂ ≅ 𝟙_ A) :
    Nonempty ((ihom ((DerivedCategory.singleFunctor A 0).obj S.X₃)).obj
      (𝟙_ (DerivedCategory A)) ≅
        ((DerivedCategory.singleFunctor A 0).obj S.X₃)⟦(-1 : ℤ)⟧) := by
  let s := DerivedCategory.singleFunctor A 0
  let u₁ := s.mapIso e₁ ≪≫ DerivedCategory.singleFunctorObjUnitIso A
  let u₂ := s.mapIso e₂ ≪≫ DerivedCategory.singleFunctorObjUnitIso A
  let f : 𝟙_ (DerivedCategory A) ⟶ 𝟙_ _ := u₁.inv ≫ s.map S.f ≫ u₂.hom
  let T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory A) :=
    CategoryTheory.Pretriangulated.Triangle.mk f (u₂.inv ≫ s.map S.g)
      (hs.singleδ ≫ u₁.hom⟦(1 : ℤ)⟧')
  have hT : T ∈ distTriang _ :=
    CategoryTheory.Pretriangulated.isomorphic_distinguished _
      hs.singleTriangle_distinguished _
      (CategoryTheory.Pretriangulated.Triangle.isoMk _ _ u₁.symm u₂.symm (Iso.refl _)
        (by simp [T, f, s]) (by simp [T, s]) (by
          simp only [T, CategoryTheory.Pretriangulated.Triangle.mk_mor₃, Iso.refl_hom,
            Category.id_comp, Category.assoc, Iso.symm_hom,
            ShortComplex.ShortExact.singleTriangle_mor₃]
          rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]))
  obtain ⟨h, hh⟩ := DerivedCategory.exists_distinguished_ihom_pre _ hT (𝟙_ _)
  have hrot := CategoryTheory.Pretriangulated.rot_of_distTriang _ hh
  let e := MonoidalClosed.unitNatIso.app (𝟙_ (DerivedCategory A))
  obtain ⟨e', -, -⟩ := CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso _ _ hT hrot
    (Arrow.isoMk e e (MonoidalClosed.unitNatIso_hom_app_unit_pre_app f))
  let e₃ := CategoryTheory.Pretriangulated.Triangle.π₃.mapIso e'
  exact ⟨(shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).symm.app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm⟩


private theorem canonicalDualTor
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    (K : DerivedCategory A)
    (hc : IsIso (MonoidalClosed.ihomUnitTensorToIhom K K))
    (hK : DerivedCategory.torAmplitudeIn A (-1) 0 K) :
    Nonempty (ExactPairing K ((ihom K).obj (𝟙_ (DerivedCategory A)))) ∧
      DerivedCategory.torAmplitudeIn A 0 1 ((ihom K).obj (𝟙_ (DerivedCategory A))) := by
  let D := (ihom K).obj (𝟙_ (DerivedCategory A))
  have := hc
  let pair : ExactPairing D K := MonoidalClosed.exactPairingOfIsIso K
  let := pair
  obtain ⟨br⟩ := DerivedCategory.nonempty_braidedCategory A
  let := br
  let pair' : ExactPairing K D := BraidedCategory.exactPairing_swap D K
  let := pair'
  refine ⟨⟨pair'⟩, ?_⟩
  simpa only [neg_zero, neg_neg] using
    (DerivedCategory.torAmplitudeIn_of_exactPairing (L := D) hK)


section Condensed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

private theorem condensedDualTor
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hc : IsIso (MonoidalClosed.ihomUnitTensorToIhom K K))
    (hK : DerivedCategory.torAmplitudeIn _ (-1) 0 K) :
    Nonempty (ExactPairing K (((CondensedRing.derivedHom Λ X).obj (op K)).obj (𝟙_ _))) ∧
      DerivedCategory.torAmplitudeIn _ 0 1
        (((CondensedRing.derivedHom Λ X).obj (op K)).obj (𝟙_ _)) := by
  exact canonicalDualTor K hc hK

private theorem condensedUnitQuotientDual
    {S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hs : S.ShortExact)
    (e₁ : S.X₁ ≅ Mod.regular (condensedRingObj Λ X))
    (e₂ : S.X₂ ≅ Mod.regular (condensedRingObj Λ X)) :
    Nonempty (((CondensedRing.derivedHom Λ X).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj S.X₃))).obj (𝟙_ _) ≅
        ((DerivedCategory.singleFunctor _ 0).obj S.X₃)⟦(-1 : ℤ)⟧) := by
  exact unitQuotientDual hs e₁ e₂


private theorem mappedRegularQuotientDual
    (F : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (f : End (Mod.regular Λ)) (g : Mod.regular Λ ⟶ N)
    (e : F.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ X))
    (hz : F.map f ≫ F.map g = 0)
    (hs : (ShortComplex.mk (F.map f) (F.map g) hz).ShortExact) :
    Nonempty (((CondensedRing.derivedHom Λ X).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (F.obj N)))).obj (𝟙_ _) ≅
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj N))⟦(-1 : ℤ)⟧) := by
  exact condensedUnitQuotientDual Λ X
    (S := ShortComplex.mk (F.map f) (F.map g) hz) hs e e


private theorem chartModelsDuality {Y : Scheme.{u}} (g : X ⟶ Y)
    (C : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (N : ∀ i : 𝒰.I₀,
      Mod (Sheaf (Scheme.ProEt.topology (𝒰.X i)) Ab.{u + 1}) (condensedRingObj Λ (𝒰.X i)))
    (hN : ∀ i, IsDualizable ((DerivedCategory.singleFunctor _ 0).obj (N i)) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj (N i)))
    (eN : ∀ i, (CondensedRing.upperStar Λ (𝒰.f i ≫ g)).obj C ≅ N i) :
    let K := (DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.upperStar Λ g).obj C)
    Nonempty (ExactPairing K (((CondensedRing.derivedHom Λ X).obj (op K)).obj (𝟙_ _))) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 K ∧
      DerivedCategory.torAmplitudeIn _ 0 1
        (((CondensedRing.derivedHom Λ X).obj (op K)).obj (𝟙_ _)) := by
  let M := (CondensedRing.upperStar Λ g).obj C
  have hlocal (i : 𝒰.I₀) :
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (𝒰.f i)).obj M)) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (𝒰.f i)).obj M)) := by
    exact transportSingleDualTor ((CondensedRing.upperStar Λ (𝒰.f i)).obj M) (N i)
      (((CondensedRing.upperStarComp Λ (𝒰.f i) g).app C).symm ≪≫ eN i) (hN i)
  have h := integralHeart_local_duality_descent Λ X M 𝒰 (-1) 0 hlocal
  have hd := condensedDualTor Λ X ((DerivedCategory.singleFunctor _ 0).obj M) h.1 h.2
  exact ⟨hd.1, h.2, hd.2⟩

end Condensed


private theorem residueDualRaw (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] (S : Scheme.{u}) :
    let Q := (DerivedCategory.singleFunctor _ 0).obj
      ((DerivedNakayama.pullback ℓ F S).obj (DerivedNakayama.quotientModule ℓ F 1))
    Nonempty ((((CondensedRing.derivedHom (DerivedNakayama.integerRing ℓ F) S).obj
      (op Q)).obj (𝟙_ (DerivedNakayama.Derived ℓ F S))) ≅ Q⟦(-1 : ℤ)⟧) := by
  have h := DerivedNakayama.derived_nakayama_resolution ℓ F
  let d := h.choose
  let r := h.choose_spec.2.choose
  have hres := h.choose_spec.2.choose_spec.2.choose_spec.choose_spec.2.2 S 1 (by omega)
  exact mappedRegularQuotientDual (DerivedNakayama.integerRing ℓ F) S
    (DerivedNakayama.pullback ℓ F S) (DerivedNakayama.quotientModule ℓ F 1)
    (d ^ 1) (r 1) (DerivedNakayama.regularPullbackIso ℓ F S)
    hres.1.choose hres.1.choose_spec



variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

private theorem realizedFiniteModel (X : Scheme.{u})
    (N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E))
    [Module.Finite (integralHeartScalars.{u} ℓ E) N] :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
      ((integralHeartRealization.{u} ℓ E X).obj N)) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj
      ((integralHeartRealization.{u} ℓ E X).obj N)) := by
  classical
  let O := SmallAdicCompletion.Coefficients.integers.{u} ℓ E
  let R := integralHeartScalars.{u} ℓ E
  have : IsPrincipalIdealRing O :=
    (Padic.extension_integers_dvr ℓ (SmallAdicCompletion.Coefficients.field.{u} ℓ E)
      (Padic.coefficientExtensionAbsoluteValue ℓ _)
      (spectralNorm_extends (K := Padic ℓ) (L := _))).choose_spec.choose_spec.2.2.2.2.2.2.2.2.1
  have : IsDomain R := MulEquiv.isDomain O ULift.ringEquiv.toMulEquiv
  have : IsPrincipalIdealRing R :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := O)).symm.toRingHom
      (ULift.ringEquiv (R := O)).symm.surjective
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := N)
  let p := Fintype.linearCombination R v
  have hp : Function.Surjective p :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hv
  let K := LinearMap.ker p
  have : Module.Finite R K := inferInstance
  have : Module.IsTorsionFree R K := inferInstance
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := K)
  let i : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) :=
    ModuleCat.ofHom (K.subtype.comp b.equivFun.symm.toLinearMap)
  let q : ModuleCat.of R (Fin n → R) ⟶ N := ModuleCat.ofHom p
  have hiq : i ≫ q = 0 :=
    ModuleCat.hom_ext (LinearMap.ext (fun x ↦ (b.equivFun.symm x).property))
  let S := ShortComplex.mk i q hiq
  have hs : S.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      exact ⟨b.equivFun ⟨x, hx⟩, congrArg Subtype.val (b.equivFun.symm_apply_apply _)⟩
    · rw [ModuleCat.mono_iff_injective]
      exact K.injective_subtype.comp b.equivFun.symm.injective
    · rw [ModuleCat.epi_iff_surjective]
      exact hp
  let F := integralHeartRealization.{u} ℓ E X
  obtain ⟨hlim, hcolim, hfree⟩ := integralHeartRealization_exact_free ℓ E X
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteColimits F := hcolim
  exact shortExactDualizableTor (hs.map_of_exact F) (hfree m) (hfree n)


private theorem finiteModelExists (X : Scheme.{u})
    (M : SmallAdicCompletion.Modules ℓ E X)
    (h : ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
      Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
        Nonempty (M ≅ (integralHeartRealization.{u} ℓ E X).obj N)) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj M) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let N := h.choose
  have := h.choose_spec.1
  exact transportSingleDualTor M ((integralHeartRealization.{u} ℓ E X).obj N)
    h.choose_spec.2.some (realizedFiniteModel ℓ E X N)


/-- Restriction of an integral module sheaf to a scheme, placed in degree zero.
Source: integral-heart-dualizable, the object C restricted to S
(blueprint: det-lem-int-integral-heart-dualizable). -/
abbrev integralHeartStratumComplex {X S : Scheme.{u}} (f : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X) : integralHeartDerivedCategory.{u} ℓ E S :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).obj C)

private theorem localModelsTriple {X S : Scheme.{u}} (g : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X)
    (hmodel : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ i : 𝒰.I₀, ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
        Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
        Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (𝒰.f i ≫ g)).obj C ≅ (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) :
    let K := integralHeartStratumComplex ℓ E g C
    let D := ((CondensedRing.derivedHom
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) S).obj (op K)).obj
        (𝟙_ (integralHeartDerivedCategory.{u} ℓ E S))
    Nonempty (ExactPairing K D) ∧ DerivedCategory.torAmplitudeIn _ (-1) 0 K ∧
      DerivedCategory.torAmplitudeIn _ 0 1 D := by
  exact hmodel.elim fun 𝒰 h𝒰 ↦
    chartModelsDuality (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) S g C 𝒰
      (fun i ↦ (CondensedRing.upperStar
        (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) (𝒰.f i ≫ g)).obj C)
      (fun i ↦ finiteModelExists ℓ E (𝒰.X i) _ (h𝒰 i)) (fun _ ↦ Iso.refl _)


private theorem residueDualSmall (S : Scheme.{u}) :
    Nonempty ((((CondensedRing.derivedHom
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) S).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (SmallAdicCompletion.finiteModule ℓ E S 0)))).obj
            (𝟙_ (integralHeartDerivedCategory.{u} ℓ E S))) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (SmallAdicCompletion.finiteModule ℓ E S 0))⟦(-1 : ℤ)⟧) := by
  exact residueDualRaw ℓ (SmallAdicCompletion.Coefficients.field.{u} ℓ E) S


/-- A constructible integral sheaf with finite scalar models on a stratum has an exact
pairing with its derived internal dual, Tor amplitude [-1,0], and dual Tor amplitude [0,1].
The derived dual of the residue module is that module shifted by -1.

Source: blueprint latest, integral-heart-dualizable, all assertions
(blueprint: det-lem-int-integral-heart-dualizable).

Proof: (1) On each chart choose a finite scalar presentation of its own module N.
The coefficient ring is a DVR by lem-weil-l-adic-extension-integers-dvr. The kernel
is finite by lem-weil-pbc-noetherian-submodule-finite and torsion-free as a submodule
of a finite free module, hence finite free by lem-sc-dvr-fg-torsionfree-free.
This gives a length-one finite free resolution, with ranks depending on the chart.
(2) Apply lem-integral-heart-realization-exact. Finite free terms are dualizable,
and the short-exact dualizability criterion gives dualizability of the quotient
placed in degree zero. The two-term cone is a flat model in degrees [-1,0], so the
bounded-flat Tor criterion gives that interval. Transport these assertions along
the chart-model isomorphisms and the composition comparison for inverse image.
(3) Apply lem-integral-heart-local-duality-descent on S. It makes the canonical
closed tensor-Hom comparison invertible and descends the Tor bound, tested against
every module sheaf. The closed-monoidal exact-pairing construction, with braiding,
gives evaluation and coevaluation with both triangle identities. The exact-pairing
Tor criterion reverses [-1,0] to [0,1]. The published derivedHom is this internal Hom.
(4) The uniformizer resolution 0 → O → O → O/pi → 0 computes the residue dual:
its dual two-term complex has only O/pi in degree one. Thus it is isomorphic in
the derived category to the degree-zero residue module shifted by -1. Apply this
on S to level zero (positive exponent one) of the existing quotient tower. -/
theorem integralHeartDualizable (X : Scheme.{u}) (C : SmallAdicCompletion.Modules ℓ E X)
    (_hC : IsConstantModelConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C)
    (s : Scheme.Stratification X) (a : Fin s.n)
    (_hmodel : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀, ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
        Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
        Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (𝒰.f i ≫ s.immersion a)).obj C ≅
            (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) :
    Nonempty (ExactPairing (integralHeartStratumComplex ℓ E (s.immersion a) C)
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a))))) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0
      (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
    DerivedCategory.torAmplitudeIn _ 0 1
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ∧
    Nonempty ((((CondensedRing.derivedHom
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) (s.domain a)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0)))).obj
            (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0))⟦(-1 : ℤ)⟧) := by
  exact appendFourth (localModelsTriple ℓ E (s.immersion a) C _hmodel)
    (residueDualSmall ℓ E (s.domain a))


end AlgebraicGeometry.ProEtale
