/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteLevelBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTowerEffectivity
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Constructibility under completed integral scalar extension

## Implementation details

The strict quotient tower of the extension is normalized by the balanced tensor associator.
Its first layer is scalar extension to the finite residue field; each higher target quotient
is filtered by powers of its uniformizer with that residue field as each layer, so extension
closure preserves constructibility and the cohomological interval. Normalized DVR
effectivity identifies these levels with reductions of the completed extension and gives
its derived completeness.

## References

* B. Bhatt, P. Scholze, *The pro-étale topology for schemes*, Proposition 3.5.1 and
  Lemma 6.8.2
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

universe d u

open CategoryTheory

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

private theorem finiteLevel_property_of_iso
    (n : ℕ) {A B : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l L (n + 1))} (e : A ≅ B)
    (r s : ℤ)
    (hA : AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y A)
    (hb : ∀ i : ℤ, i ∈ AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport A →
      r ≤ i ∧ i ≤ s) :
    AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y B ∧
    ∀ i : ℤ, i ∈ AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport B →
      r ≤ i ∧ i ≤ s := by
  let : Finite (Padic.coefficientExtensionRing l L (n + 1)) :=
    Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  let P := AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) Y
  have : P.IsClosedUnderIsomorphisms :=
    (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated Y
      (Padic.coefficientExtensionRing l L (n + 1))).1
  refine ⟨P.prop_of_iso e hA, ?_⟩
  intro i hi
  apply hb i
  exact fun hz ↦ hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)

/-- Completed integral extension preserves the actual integral constructible property. -/
theorem integralScalarExtension_constructible
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralScalarExtension l E L ι Y).obj K.obj) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  let X := (DerivedCategory.Q (C := integralTowerModules l E Y)).objPreimage K.obj
  let eX := (DerivedCategory.Q (C := integralTowerModules l E Y)).objObjPreimageIso K.obj
  obtain ⟨V, f, hV, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) X
  have hgood : integralOperationsGoodComplex l E Y V := by
    refine ⟨hV, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (V.X i)).symm (hf i)
  let P : (integralOperationsGoodComplex l E Y).FullSubcategory := ⟨V, hgood⟩
  let : QuasiIso f := hq
  let e : (DerivedCategory.Q.obj P.obj : DerivedCategory (integralTowerModules l E Y)) ≅
      K.obj := asIso (DerivedCategory.Q.map f) ≪≫ eX
  have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso
    e.symm K.property
  obtain ⟨_, r, s, hrs, hlevels⟩ := hP
  have hfinite := integralScalarFiniteLevel_bounds D l hl E L ι Y P r s hrs
    (hlevels 0).1 (hlevels 0).2
  obtain ⟨hc, he⟩ := integralScalarTower_effectivity D l hl E L ι Y P
  have hresult : boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)) := by
    refine ⟨hc, r, s, hrs, ?_⟩
    intro n
    obtain ⟨en⟩ := he n
    exact finiteLevel_property_of_iso l L Y n en.symm r s (hfinite n).1 (hfinite n).2
  exact (boundedConstructibleDerivedCompleteIntegral D l hl L Y).prop_of_iso
    ((integralScalarExtension l E L ι Y).mapIso e) hresult

/-- The restricted functor uses the original completed extension on objects and maps. -/
noncomputable def constructibleIntegralScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralScalarExtension l E L ι Y)
    (integralScalarExtension_constructible D l hl E L ι Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Integer-linearity of the restricted completed coefficient functor. -/
theorem constructibleIntegralScalarExtension_smul
    (K K' : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralScalarExtension D l hl E L ι Y).map (a • f) =
      integralScalarIntegerInclusion l E L ι a •
        (constructibleIntegralScalarExtension D l hl E L ι Y).map f := by
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  let : Linear (Padic.coefficientExtensionIntegers l L)
      (completedIntegralDerivedCategory l L Y D hl) := integralCoefficientLinear l L Y
  apply ObjectProperty.hom_ext
  change (integralScalarExtension l E L ι Y).map (a • f.hom) =
    integralScalarIntegerInclusion l E L ι a •
      (integralScalarExtension l E L ι Y).map f.hom
  rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec,
    (integralCoefficientLinear_existsUnique l L Y).exists.choose_spec]
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures

namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private local instance scalarSiteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} _

private noncomputable local instance scalarSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private local instance scalarLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y

private theorem scalarMap_eq_completed :
    integralCompletedScalarMap l E L ι Y = completedCoefficientMap l E L ι Y := by
  apply (completedCoefficientMap_existsUnique l E L ι Y).unique
  · exact (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec
  · exact (completedCoefficientMap_existsUnique l E L ι Y).exists.choose_spec

attribute [local irreducible] integralCompletedScalarMap completedCoefficientMap
  completedScalarChangeData

set_option backward.isDefEq.respectTransparency false in
private theorem tensorPresentation_hom_ext
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : Y.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem tensorPresentation_transport
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (U : Y.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom ((hA.trans (congrArg
      (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans
        hB.symm)).val.app U
      ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom hB.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  subst ψ
  subst A
  subst B
  rfl

private theorem tensorPresentation_natural
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N)
    (A B C F : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N)
    (hC : C = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hF : F = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ N)
    (a : A ⟶ B) (b : C ⟶ F)
    (ha : a = eqToHom hA ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M f ≫ eqToHom hB.symm)
    (hb : b = eqToHom hC ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} ψ M f ≫ eqToHom hF.symm) :
    a ≫ eqToHom ((hB.trans (congrArg
      (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N) hφ)).trans
        hF.symm) =
      eqToHom ((hA.trans (congrArg
        (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans
          hC.symm) ≫ b := by
  subst ψ
  subst A
  subst B
  subst C
  subst F
  simpa using ha.trans hb.symm

attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private noncomputable def ordinaryScalarModelIso :
    integralOrdinaryScalar l E L ι Y ≅ completedOrdinaryScalarExtension l E L ι Y := by
  have hF : ∀ M, (integralOrdinaryScalar l E L ι Y).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralCompletedScalarMap l E L ι Y) M :=
    by
      simpa only [integralOrdinaryScalar] using
        (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
  have hG : ∀ M, (completedOrdinaryScalarExtension l E L ι Y).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (completedCoefficientMap l E L ι Y) M :=
    by
      simpa only [completedOrdinaryScalarExtension] using
        (completedScalarChangeData l E L ι Y).choose_spec.choose
  have hφ := scalarMap_eq_completed l E L ι Y
  have hobj (M : integralTowerModules l E Y) := ((hF M).trans (congrArg
    (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans (hG M).symm
  refine NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) ?_
  intro M N f
  exact tensorPresentation_natural Y _ _ hφ M N f _ _ _ _ (hF M) (hF N)
    (hG M) (hG N) _ _
    (by simpa only [integralOrdinaryScalar] using
      (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose f)
    (by simpa only [completedOrdinaryScalarExtension] using
      (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose f)

private theorem ordinaryScalarModelIso_hom_app (M : integralTowerModules l E Y) :
    (ordinaryScalarModelIso l E L ι Y).hom.app M =
      eqToHom ((((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M).trans
        (congrArg (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
          (scalarMap_eq_completed l E L ι Y))).trans
        ((completedScalarChangeData l E L ι Y).choose_spec.choose M).symm) := by
  rfl

attribute [local irreducible] ordinaryScalarModelIso
attribute [local semireducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem ordinaryScalarModelIso_transport
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : M.val.obj U) :
    ((ordinaryScalarModelIso l E L ι Y).hom.app M).val.app U
      ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M).symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf
            (integralCompletedScalarMap l E L ι Y) M).presheaf).app U
              (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
      completedScalarTensorSection l E L ι Y M U s x := by
  rw [ordinaryScalarModelIso_hom_app]
  exact tensorPresentation_transport Y _ _ (scalarMap_eq_completed l E L ι Y)
    M _ _ ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M)
    ((completedScalarChangeData l E L ι Y).choose_spec.choose M) U s x

attribute [local irreducible] completedScalarTensorSection

attribute [local irreducible] integralScalarReductionWitness integralScalarReduction
  integralScalarTensorSection

private theorem complexProduct_hom_ext
    {D : Type*} [Category* D] [Preadditive D] [HasCountableProducts D]
    (X : ℕ → CochainComplex D ℤ) (i : ℤ) {M : D}
    (f g : M ⟶ (∏ᶜ X).X i)
    (h : ∀ n, f ≫ (Pi.π X n).f i = g ≫ (Pi.π X n).f i) : f = g := by
  apply (isLimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i)
    (limit.isLimit (Discrete.functor X))).hom_ext
  intro n
  exact h n.as

attribute [local irreducible] limit

private theorem cocone_degree_ext
    {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
    {P K L₀ : CochainComplex D ℤ} (φ : K ⟶ L₀)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

/-- Derived completeness for one finite-field presentation implies unrestricted completeness:
both are equivalent to the presentation-free Roos condition. -/
private theorem isDerivedCompleteUnrestricted_of_isDerivedComplete
    (K : completedIntegralDerivedCategory l E Y D hl)
    (hK : IsDerivedComplete l E Y D hl K) : IsDerivedCompleteUnrestricted l E Y K := by
  have hsf := (sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D' : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl' : l ≠ D'.p := by
    change l ≠ p
    omega
  exact ⟨D', hl', (sfDerivedComplete_iff_legacy l E Y D' hl' K).mp hsf⟩

/-- On a good complex with complete localization, the strict-cone chain comparison is a
quasi-isomorphism: the universal counit is invertible on K-flat complexes and the descended
comparison is invertible on complete objects. -/
private theorem completedScalarChainComparison_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hc : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj P.obj)) :
    IsIso (DerivedCategory.Q.map ((completedScalarChainComparison l E L ι Y).app P.obj)) := by
  have h := (completedScalarComparison_existsUnique l E L ι Y).exists.choose_spec P
  have h1 : IsIso ((completedScalarComparison_existsUnique l E L ι Y).exists.choose.app
      (DerivedCategory.Q.obj P.obj)) :=
    ((finiteFreeCompletedScalarComparison l E L ι Y).2.1 _ hc).1
  have h2 : IsIso (completedScalarCounit l E L ι Y P.obj) :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.2.2 P.obj P.property.1
  have h3 := IsIso.comp_isIso' h1
    (inferInstance : IsIso ((integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P))
  rw [h] at h3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h2 h3

/-- On a good complex with complete localization, ordinary exact extension agrees with the
completed extension, through the quotient completion chain map. -/
private noncomputable def ordinaryScalarCompletedIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hc : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj P.obj)) :
    (integralOrdinaryDerivedScalar l E L ι Y).obj (DerivedCategory.Q.obj P.obj) ≅
      (integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj) :=
  (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.app P.obj ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)).app
        P.obj) ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map ((completedScalarChainComparison l E L ι Y).app P.obj))
      (completedScalarChainComparison_isIso l E L ι Y P hc) ≪≫
    ((integralScalarExtensionComparison l E L ι Y).app P).symm

/-- Every object of the derived category is the localization of a good complex. -/
private theorem exists_goodComplex_iso (K : DerivedCategory (integralTowerModules l E Y)) :
    ∃ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let := integralOperationsGoodLocalization_isLocalization l E Y
  have := Localization.essSurj (integralOperationsGoodLocalization l E Y)
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι)
  exact ⟨(integralOperationsGoodLocalization l E Y).objPreimage K,
    ⟨(integralOperationsGoodLocalization l E Y).objObjPreimageIso K⟩⟩

/-- Finite free completed extension preserves bounded constructibility and completeness. -/
theorem integralOrdinaryDerivedScalar_constructible
    (K : completedIntegralDerivedCategory l E Y D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E Y K) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_goodComplex_iso l E Y K
  have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso e.symm hK
  have hc := isDerivedCompleteUnrestricted_of_isDerivedComplete D l hl E Y _ hP.1
  exact (boundedConstructibleDerivedCompleteIntegral D l hl L Y).prop_of_iso
    ((ordinaryScalarCompletedIso l E L ι Y P hc).symm ≪≫
      (integralOrdinaryDerivedScalar l E L ι Y).mapIso e)
    (integralScalarExtension_constructible D l hl E L ι Y ⟨_, hP⟩)

/-- Restriction of finite free completed tensor to the integral full subcategories.
On complete objects its ordinary exact tensor model computes completed derived tensor. -/
noncomputable def integralConstructibleScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property)

/-- The actual boundary 1-s of the fixed scalar tower, used for both cone coordinates. -/
noncomputable abbrev integralScalarRoosBoundary
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
    (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P))

attribute [local irreducible] completedScalarChainComparison

private theorem integralScalarCompletionChain_model_spec :
    let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ);
    let b := e.hom ≫ completedScalarChainComparison l E L ι Y;
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((b.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (b.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)
  let b := e.hom ≫ completedScalarChainComparison l E L ι Y
  change _ ∧ _
  constructor
  · intro P i n U s x
    dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change (((completedScalarChainComparison l E L ι Y).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
      (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
      ).val.app U
        (((ordinaryScalarModelIso l E L ι Y).hom.app (P.X i)).val.app U
          ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
            (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf
                (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                  (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                    ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x)))) = _
    exact (congrArg (fun z ↦
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
        ).val.app U z) (ordinaryScalarModelIso_transport l E L ι Y (P.X i) U s x)).trans
      (by
        simpa only [completedScalarChainComparison] using
          (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.1
            P i n U s x)
  · intro P i j hij
    have hj : j = i - 1 := by omega
    subst j
    change (e.hom.app P).f i ≫
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega)) = 0
    have h : ((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega) = 0 := by
      simpa only [completedScalarChainComparison] using
        (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.2 P i
    dsimp only [completedOrdinaryScalarComplex] at h ⊢
    exact (congrArg ((e.hom.app P).f i ≫ ·) h).trans
      (Preadditive.leftComp _ ((e.hom.app P).f i)).map_zero

/-- The completion chain map is fixed by the quotient maps and zero shifted coordinate. -/
theorem integralScalarCompletionChain_existsUnique :
    ∃! χ : (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
        integralScalarComplexFunctor l E L ι Y,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((χ.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (χ.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let e := NatIso.mapHomologicalComplex
      (ordinaryScalarModelIso l E L ι Y) (.up ℤ)
    let b := e.hom ≫ completedScalarChainComparison l E L ι Y
    exact ⟨b, integralScalarCompletionChain_model_spec l E L ι Y⟩
  · intro b₁ b₂ hb₁ hb₂
    apply NatTrans.ext
    funext P
    ext i : 1
    let φ := integralScalarRoosBoundary l E L ι Y P
    have hf : (b₁.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
        (b₂.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i := by
      apply complexProduct_hom_ext
      intro n
      change ((b₁.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i ≫ _) =
        ((b₂.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i ≫ _)
      apply tensorPresentation_hom_ext Y (integralCompletedScalarMap l E L ι Y)
        (P.X i) ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) _
        ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose (P.X i))
      intro U s x
      exact (hb₁.1 P i n U s x).trans (hb₂.1 P i n U s x).symm
    have hs := (hb₁.2 P i (i - 1) (by omega)).trans
      (hb₂.2 P i (i - 1) (by omega)).symm
    exact cocone_degree_ext φ (b₁.app P) (b₂.app P) i hf hs

/-- The quotient completion map, with both cone coordinates specified. -/
noncomputable def integralScalarCompletionChain :=
  (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose

private theorem integralScalarCompletionChain_model :
    integralScalarCompletionChain l E L ι Y =
      (NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)).hom ≫
        completedScalarChainComparison l E L ι Y := by
  exact (integralScalarCompletionChain_existsUnique l E L ι Y).unique
    (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose_spec
    (integralScalarCompletionChain_model_spec l E L ι Y)

/-- On a good complex with complete localization, the quotient completion chain map is a
quasi-isomorphism. -/
private theorem integralScalarCompletionChain_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hc : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj P.obj)) :
    IsIso (DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj)) := by
  rw [integralScalarCompletionChain_model, NatTrans.comp_app, Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (completedScalarChainComparison_isIso l E L ι Y P hc)

/-- The localized quotient completion map from ordinary to completed extension, normalized on
good representatives by the quotient completion chain map. -/
private theorem integralScalarCompletion_exists :
    ∃ τ : integralOrdinaryDerivedScalar l E L ι Y ⟶ integralScalarExtension l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        τ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  let := integralOperationsGoodLocalization_isLocalization l E Y
  let Λ := integralOperationsGoodLocalization l E Y
  let ff := Localization.fullyFaithfulWhiskeringLeft Λ
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι) (DerivedCategory (integralTowerModules l L Y))
  let α : Λ ⋙ integralOrdinaryDerivedScalar l E L ι Y ⟶ integralScalarOnGood l E L ι Y :=
    Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι
      ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom ≫
        Functor.whiskerRight (integralScalarCompletionChain l E L ι Y) DerivedCategory.Q)
  refine ⟨ff.preimage (α ≫ (integralScalarExtensionComparison l E L ι Y).inv), fun P ↦ ?_⟩
  have h : (ff.preimage (α ≫ (integralScalarExtensionComparison l E L ι Y).inv)).app
      (DerivedCategory.Q.obj P.obj) =
        α.app P ≫ (integralScalarExtensionComparison l E L ι Y).inv.app P :=
    NatTrans.congr_app
      (ff.map_preimage (α ≫ (integralScalarExtensionComparison l E L ι Y).inv)) P
  rw [h]
  exact (Category.assoc _ _ _).trans ((congrArg (α.app P ≫ ·)
    ((integralScalarExtensionComparison l E L ι Y).inv_hom_id_app P)).trans (Category.comp_id _))


/-- The canonical finite-free comparison is uniquely fixed on good representatives. -/
theorem integralConstructibleScalarComparison_existsUnique :
    ∃! c : integralConstructibleScalarExtension D l hl E L ι Y ≅
        constructibleIntegralScalarExtension D l hl E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : boundedConstructibleDerivedCompleteIntegral D l hl E Y
          (DerivedCategory.Q.obj P.obj)),
        (c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩).hom ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  obtain ⟨τ, hτ⟩ := integralScalarCompletion_exists l E L ι Y
  have hiso (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
      IsIso (τ.app K.obj) := by
    obtain ⟨P, ⟨e⟩⟩ := exists_goodComplex_iso l E Y K.obj
    have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso
      e.symm K.property
    have hc := isDerivedCompleteUnrestricted_of_isDerivedComplete D l hl E Y _ hP.1
    refine (NatTrans.isIso_app_iff_of_iso τ e).1 ?_
    have := integralScalarCompletionChain_isIso l E L ι Y P hc
    have h3 : IsIso (τ.app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparison l E L ι Y).hom.app P) := by
      rw [hτ P]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (Iso.isIso_hom ((integralScalarExtensionComparison l E L ι Y).app P)) h3
  let c₀ : integralConstructibleScalarExtension D l hl E L ι Y ≅
      constructibleIntegralScalarExtension D l hl E L ι Y :=
    NatIso.ofComponents
      (fun K ↦ (boundedConstructibleDerivedCompleteIntegral D l hl L Y).isoMk
        (@asIso _ _ _ _ (τ.app K.obj) (hiso K)))
      (fun f ↦ ObjectProperty.hom_ext _ (τ.naturality f.hom))
  refine ⟨c₀, fun P hP ↦ hτ P, fun c hc ↦ ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨P, ⟨e⟩⟩ := exists_goodComplex_iso l E Y K.obj
  have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso
    e.symm K.property
  let e' : (⟨DerivedCategory.Q.obj P.obj, hP⟩ :
      boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) ≅ K :=
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).isoMk e
  have hK : c.hom.app ⟨_, hP⟩ = c₀.hom.app ⟨_, hP⟩ := ObjectProperty.hom_ext _
    ((cancel_mono ((integralScalarExtensionComparison l E L ι Y).hom.app P)).1
      ((hc P hP).trans (hτ P).symm))
  rw [← cancel_epi ((integralConstructibleScalarExtension D l hl E L ι Y).map e'.hom),
    c.hom.naturality, NatTrans.naturality]
  exact congrArg (· ≫ (constructibleIntegralScalarExtension D l hl E L ι Y).map e'.hom) hK

/-- The finite-free comparison with the canonical quotient completion normalization. -/
noncomputable def integralConstructibleScalarComparison :=
  (integralConstructibleScalarComparison_existsUnique D l hl E L ι Y).exists.choose

end WeilConjectures
