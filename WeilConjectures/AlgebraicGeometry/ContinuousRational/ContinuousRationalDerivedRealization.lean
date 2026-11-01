/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleRationalHomComparison
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiniteFreeCriterion
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiltrationModels
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousPullbackTransport
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousComparisonCoherence
import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationScalarCoherence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting

/-! # Continuous rational derived realization

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

The data declarations are reexported from `ContinuousRationalRealizationData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pbcRationalCoefficientEquiv pbcIntegralDatum
  reductionDerivedChange completedAdicDerivedChange
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory

section Ambient

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

end Ambient

private def coefficientEncoding (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      rationalCoefficientSheaf l X E := by
  let := coefficientExtensionNormedField l E
  let e := WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact
    { hom := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ⟨fun x ↦ ULift.up (e (f.down x)),
                continuous_uliftUp.comp (he.continuous.comp f.down.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up ⟨fun x ↦ e.symm (f x).down,
                hei.continuous.comp (continuous_uliftDown.comp f.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }

private theorem coefficientEncoding_normalization (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
    (x : U.unop.left) :
    rationalCoefficientValue l E X U ((coefficientEncoding l E X).hom.hom.app U (ULift.up f)) x
      = WithAbs.ofAbs (f x) := by
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem preserve0 (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    ((localizedT l E X).le 0 K → (s.J.obj K).IsLE 0) ∧
      ((localizedT l E X).ge 0 K → (s.J.obj K).IsGE 0) := by
  let t := localizedT l E X
  let B := pbcAdicCompletion X.scheme (pbcIntegralDatum l E)
  let R := rationalCoefficientSheaf l X.scheme E
  let φ := s.integralIso.hom ≫ s.inclusion
  have := s.ordinary_exact.1
  have := s.ordinary_exact.2
  have hz (L : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) (r : ℤ)
      (h : IsZero ((DerivedCategory.homologyFunctor _ r).obj L.obj)) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
          (pbcUniformizer l E)).obj L))) := by
    let a := (s.cohomology r).app L.obj
    have he : s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L) = (pbcDerivedExtend φ).obj L.obj := s.objects L
    rw [he]
    exact ((pbcExtend φ).map_isZero h).of_iso a
  constructor
  · intro hk
    obtain ⟨L, hL, ⟨e⟩⟩ := (pbc_localized_tstructure X.scheme l E).choose_spec.1 K |>.1.mp hk
    have hL' : L.obj.IsLE 0 :=
      (ObjectProperty.tStructure_isLE_iff
        (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
        (pbcAmbientTStructure X.scheme l E) L 0).mp ⟨hL⟩
    have hq : (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L)).IsLE 0 :=
      (DerivedCategory.isLE_iff _ _).mpr (fun r hr ↦
        hz L r (DerivedCategory.isZero_of_isLE L.obj 0 r hr))
    exact DerivedCategory.TStructure.t.isLE_of_iso (s.J.mapIso e).symm 0
  · intro hk
    obtain ⟨L, hL, ⟨e⟩⟩ := (pbc_localized_tstructure X.scheme l E).choose_spec.1 K |>.2.mp hk
    have hL' : L.obj.IsGE 0 :=
      (ObjectProperty.tStructure_isGE_iff
        (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
        (pbcAmbientTStructure X.scheme l E) L 0).mp ⟨hL⟩
    have hq : (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L)).IsGE 0 :=
      (DerivedCategory.isGE_iff _ _).mpr (fun r hr ↦
        hz L r (DerivedCategory.isZero_of_isGE L.obj 0 r hr))
    exact DerivedCategory.TStructure.t.isGE_of_iso (s.J.mapIso e).symm 0

private theorem preserve (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (r : ℤ) :
    ((localizedT l E X).le r K → (s.J.obj K).IsLE r) ∧
      ((localizedT l E X).ge r K → (s.J.obj K).IsGE r) := by
  let t := localizedT l E X
  let a := DerivedCategory.TStructure.t (C :=
    pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  have := s.shift
  constructor
  · intro hk
    have hk' : t.IsLE K r := ⟨hk⟩
    have hshift : t.IsLE (K⟦r⟧) 0 := t.isLE_shift K r r 0 (by omega)
    have hj : a.IsLE (s.J.obj (K⟦r⟧)) 0 :=
      (preserve0 l E X s (K⟦r⟧)).1 hshift.le
    have hq : a.IsLE ((s.J.obj K)⟦r⟧) 0 :=
      a.isLE_of_iso (show s.J.obj (K⟦r⟧) ≅ (s.J.obj K)⟦r⟧ from
        (s.J.commShiftIso r).app K) 0
    exact (a.isLE_of_shift (s.J.obj K) r r 0 (by omega))
  · intro hk
    have hk' : t.IsGE K r := ⟨hk⟩
    have hshift : t.IsGE (K⟦r⟧) 0 := t.isGE_shift K r r 0 (by omega)
    have hj : a.IsGE (s.J.obj (K⟦r⟧)) 0 :=
      (preserve0 l E X s (K⟦r⟧)).2 hshift.ge
    have hq : a.IsGE ((s.J.obj K)⟦r⟧) 0 :=
      a.isGE_of_iso (show s.J.obj (K⟦r⟧) ≅ (s.J.obj K)⟦r⟧ from
        (s.J.commShiftIso r).app K) 0
    exact (a.isGE_of_shift (s.J.obj K) r r 0 (by omega))

end AlgebraicGeometry.Scheme.ContinuousRational
