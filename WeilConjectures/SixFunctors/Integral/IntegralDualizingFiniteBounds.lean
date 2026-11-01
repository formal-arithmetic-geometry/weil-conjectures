/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDualizingRoosModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! # Uniform bounds for the finite dualizing terms

Source: current blueprint prop-coef-integral-dualizing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 2000] CommRing.toRing

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finiteBounds_constructible
    (A : Type (u + 1)) [CommRing A] [Finite A] (Y : Scheme.{u})
    (K : Etale.DerivedCategoryModule A Y)
    (h : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K) :
    Etale.DerivedCategory.isBoundedConstructible A Y K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := h
  refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hc i), min a b, b, min_le_right _ _, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · exact (DerivedCategory.isGE_iff K a).1 ha i (hi.trans_le (min_le_left _ _))
  · exact (DerivedCategory.isLE_iff K b).1 hb i hi

include hl in
/-- Constructibility, support and Tor bounds for an object identified with a finite
exceptional dualizing term. This is a finite-coefficient assertion, uniform in n.

Source: current blueprint prop-coef-integral-dualizing, first proof paragraph,
constant-input preservation bound (blueprint: lem-coef-integral-dualizing-finite-bounds).

Proof: the etale constant coefficient unit is constructible and flat in degree zero.
Apply verdier_preservation_strata to this input with interval [0,0]. Evaluation at
its unit identifies its internal derived Hom with the finite etale dualizing object.
The finite duality site comparison transports that object and the Tor interval to
pro-etale coefficients. The prescribed finiteDualizingOrigin identifies it with
integralDualizingFiniteTerm. Test Tor amplitude on the regular coefficient module to
obtain the cohomological support bound in [-2d,0]. Finally transport all three
properties along e: homology carries isomorphisms to isomorphisms, constructibility
is invariant under them, and every representative of M is also a representative of
the finite term after composing with e. This argument works for n=0 (the residue
coefficient), d=0, the empty scheme, and zero objects. -/
theorem integralDualizing_finite_bounds (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (n : ℕ)
    (M : DerivedCategory (scalarReductionTarget l E X n))
    (e : M ≅ integralDualizingFiniteTerm l E D X n) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X M ∧
      proEtaleCohomologicalSupport M ⊆ Set.Icc (-(2 * (d : ℤ))) 0 ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        M (-(2 * (d : ℤ))) 0 := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  let A := finiteDualizingCoeff l E n
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let ωe := finiteDualizingEtaleTerm l E D X n
  have hunit : Etale.DerivedCategory.isBoundedConstructible A X (𝟙_ (DerivedCategory C)) :=
    finiteBounds_constructible A X _ (Etale.constructibleFiniteTor_unit A).1
  have htorunit : Etale.DerivedCategory.hasTorAmplitudeIn A X 0 0
      (𝟙_ (DerivedCategory C)) := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    exact (Etale.DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  obtain ⟨hc, ht⟩ := verdier_preservation_strata D l hl E (n + 1) (by omega)
    X d hd 0 0 (𝟙_ (DerivedCategory C)) hunit htorunit
  let eu : ((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj
      (op (𝟙_ (DerivedCategory C)))).obj ωe ≅ ωe :=
    (MonoidalClosed.unitNatIso.app ωe).symm
  have hce : Etale.DerivedCategory.isBoundedConstructible A X ωe := by
    apply finiteBounds_constructible A X ωe
    apply (Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso eu
    exact (by
          obtain ⟨hc, a, b, _hab, hz⟩ := hc
          refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, ?_⟩
          · exact (DerivedCategory.isGE_iff _ a).2 (fun i hi ↦ hz i (.inl hi))
          · exact (DerivedCategory.isLE_iff _ b).2 (fun i hi ↦ hz i (.inr hi))
          · exact fun i ↦
              (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i))
  have hte : Etale.DerivedCategory.hasTorAmplitudeIn A X (-(2 * (d : ℤ))) 0 ωe := by
    intro F i hi
    have hz := ht F i (by simpa only [neg_zero, zero_sub] using hi)
    exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso eu).app
        ((DerivedCategory.singleFunctor C 0).obj F))).symm
  obtain ⟨hcc, htt⟩ := finiteCoefficient_comparison_preserves_torAmplitude
    D l hl E (n + 1) (by omega) X (-(2 * (d : ℤ))) 0 (by omega) ωe hce hte
  let comparison := ProEtale.finiteCoefficientIntrinsicDerivedComparison X
    (Padic.coefficientExtensionRing l E (n + 1))
  let eω : comparison.obj ωe ≅ integralDualizingFiniteTerm l E D X n :=
    (Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (n + 1)))).app ωe ≪≫
      finiteDualizingOrigin l E D X n
  let eM : comparison.obj ωe ≅ M := eω ≪≫ e.symm
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
    (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
  have hMc : intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X M :=
    ObjectProperty.prop_of_iso _ eM hcc
  have hMt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      M (-(2 * (d : ℤ))) 0 := by
    refine ⟨htt.1, ?_⟩
    intro L P hL f hf hP V i hi
    exact htt.2 L P (hL.map (fun e ↦ e ≪≫ eM.symm)) f hf hP V i hi
  refine ⟨hMc, ?_, hMt⟩
  obtain ⟨P, hP, hz, ⟨eP⟩⟩ :=
    (finiteCoefficient_torAmplitude_iff_flatModel D l hl E (n + 1) (by omega)
      X M hMc _ _ hMt.1).1 hMt
  intro i hi
  by_contra h
  have hi' : i < -(2 * (d : ℤ)) ∨ 0 < i := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  apply hi
  have he := (HomologicalComplex.exactAt_iff_isZero_homology P i).1
    (HomologicalComplex.ExactAt.of_isZero (hz i hi'))
  exact he.of_iso
    ((DerivedCategory.homologyFunctor (scalarReductionTarget l E X n) i).mapIso eP ≪≫
      (DerivedCategory.homologyFunctorFactors (scalarReductionTarget l E X n) i).app P)

end WeilConjectures
