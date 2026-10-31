/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! # Finite intrinsic Verdier bounds

Source: blueprint thm-coef-integral-verdier, finite preservation argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- Finite intrinsic Verdier duality preserves constructibility and the geometric Tor
interval. This is a finite-coefficient assertion; there is no integral completeness premise.

Source: current blueprint thm-coef-integral-verdier, first proof paragraph;
lem-weil-verdier-preservation-strata and lem-weil-finite-duality-site-comparison
(blueprint: lem-sf-finite-intrinsic-verdier-bounds).

Proof: the constructible descent theorem chooses an etale finite-Tor origin and
reflects the specified Tor interval to it. Geometric duality of the etale unit
makes the etale dualizing complex finite-Tor constructible. Apply
lem-weil-verdier-preservation-strata with the supplied dimension bound d.
The normalized site Hom comparison is an isomorphism on this pair. Compose the
exact-functor composition isomorphism with finiteDualizingOrigin to identify
the comparison image of the etale dualizing object with the prescribed intrinsic
object. The origin isomorphism and this dualizing isomorphism identify the
comparison image of the etale dual with the intrinsic dual. Constructibility
is closed under isomorphisms. The Tor predicate transports by precomposing its
representative isomorphisms. Finally the finite-coefficient flat-model theorem
gives a representative whose terms vanish outside the stated interval.
Its homology vanishes there, and the homology localization comparison proves
the cohomological support bound. The argument includes the residue index n=0,
the empty scheme, and zero input without a nonemptiness premise. -/
theorem finiteIntrinsicVerdier_bounds (n : ℕ)
    (M : DerivedCategory (scalarReductionTarget.{u, u} l E X n))
    (hM : intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X M)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1)) M a b) :
    let N := (finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj (op M)
    intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X N ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        N (-b - 2 * (d : ℤ)) (-a) ∧
      proEtaleCohomologicalSupport N ⊆ Set.Icc (-b - 2 * (d : ℤ)) (-a) := by
  classical
  have hab := hTor.1
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  let := (finiteDualizingCompactification D X).hasCompactification
  let ωe := finiteDualizingEtaleTerm l E D X n
  have hω : finiteTorConstructibleEtale l E (n + 1) (by omega) X ωe := by
    apply (finiteTorConstructibleEtale_iff_source l E (n + 1) (by omega) X ωe).2
    exact Etale.constructibleFiniteTor_dualizingComplex A (𝟙 _) _
      (Etale.constructibleFiniteTor_unit A)
  have hdesc := (coefFiniteHomSiteDescent D l hl E X).1 n
  have hctf : finiteTorConstructible l E (n + 1) (by omega) X M :=
    ⟨hM, a, b, hTor⟩
  obtain ⟨Me, hMe, ⟨eM⟩⟩ := hdesc.2.2.1 M hctf
  have hTe := (hdesc.2.2.2.1 M Me hctf hMe.1 ⟨eM⟩ a b hTor.1).2 hTor
  have hdual := verdier_preservation_strata D l hl E (n + 1) (by omega)
    X d hd a b Me hMe.1 hTe
  let Ne := (finiteHomEtaleInternalHom l E X n).obj (op Me, ωe)
  have hNe : finiteTorConstructibleEtale l E (n + 1) (by omega) X Ne := by
    exact ⟨hdual.1, -b - 2 * (d : ℤ), -a, by omega, hdual.2⟩
  obtain ⟨βe, βp, hβe, hβp, hsym, hcal⟩ := (coefFiniteHomSiteDescent D l hl E X).2
  have hi := ((hcal n n (le_refl n)).2.2.2.2.1 Me ωe hMe hω).1
  let eω : (finiteHomNu l E X n).obj ωe ≅ integralDualizingFiniteTerm l E D X n :=
    (@Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2,
        u + 1, u + 1, u + 1, u + 1, u + 1, u + 2}
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))))
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))))
      (scalarReductionTarget.{u, u} l E X n)
      _ _ _ _ _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.standard _)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (n + 1)))
      inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (n + 1))).2.1
      inferInstance inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (n + 1))).2.2.1
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (n + 1))).2.2.2).app ωe ≪≫
      finiteDualizingOrigin l E D X n
  let α : (finiteHomNu l E X n).obj Ne ≅
      (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj
        (op ((finiteHomNu l E X n).obj Me), (finiteHomNu l E X n).obj ωe) :=
    @asIso _ _ _ _ (finiteHomSiteHom l E X n Me ωe) hi
  let eN : (finiteHomNu l E X n).obj Ne ≅
      (finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj (op M) :=
    α ≪≫
      (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).mapIso
        (Iso.prod eM.symm.op eω)
  have hN' := hdesc.2.2.2.2 Ne hNe
  have hNtor := hN'.2 (-b - 2 * (d : ℤ)) (-a) (by omega) hdual.2
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
    (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
  have hNc := ObjectProperty.prop_of_iso _ eN hN'.1.1
  have hNt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj (op M))
      (-b - 2 * (d : ℤ)) (-a) := by
    refine ⟨hNtor.1, ?_⟩
    intro L P hL f hf hP V i hi
    exact hNtor.2 L P (hL.map (fun e ↦ e ≪≫ eN.symm)) f hf hP V i hi
  refine ⟨hNc, hNt, ?_⟩
  obtain ⟨P, hP, hz, ⟨eP⟩⟩ :=
    (finiteCoefficient_torAmplitude_iff_flatModel D l hl E (n + 1) (by omega)
      X _ hNc _ _ hNt.1).1 hNt
  intro i hi
  by_contra h
  have hi' : i < -b - 2 * (d : ℤ) ∨ -a < i := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  apply hi
  have he := (HomologicalComplex.exactAt_iff_isZero_homology P i).1
    (HomologicalComplex.ExactAt.of_isZero (hz i hi'))
  exact he.of_iso
    ((DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X n) i).mapIso eP ≪≫
      (DerivedCategory.homologyFunctorFactors
        (scalarReductionTarget.{u, u} l E X n) i).app P)

end WeilConjectures.IntegralVerdier
