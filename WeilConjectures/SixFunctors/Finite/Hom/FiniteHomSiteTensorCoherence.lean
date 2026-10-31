/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleTensorLaws
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedTensorFunctorLaws
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorMateEquations
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteQuotientCoherence
import WeilConjectures.SixFunctors.Coefficient.CoefficientMonoidalSquareUnit

/-! # A component of finite Hom site descent

Source: blueprint `lem-coef-finite-hom-site-descent`, final site comparison argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The canonical tensor comparisons form a coherent symmetric monoidal site/scalar
square for the prescribed Koszul symmetry. This assertion contains no Hom comparison.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof steps 2--4
(blueprint: lem-coef-finite-hom-site-tensor-coherence).

Proof: take the finite tensor coherence witness retained in the published calculus fibers.
The separately normalized functor laws supply the strong site and intrinsic quotient
functors and their signed symmetry equations. Convert the published etale domain calculus
to the fixed etale tensorator. The fixed-mate tensor equation and the four strong witnesses
imply the unit equation by the generic monoidal-square unit theorem. For quotient towers,
compose the ordinary normalized restriction comparisons on local generators, descend that
equality by exact derived-square composition, apply the mate composition formula and invert.
Combine the square, symmetry equations and proved quotient coherence. -/
theorem finiteHomSiteTensorCoherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
      (finiteHomEtaleClosed l E X n).monoidal)
    (hβet : ∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
      HEq ((βet n).toBraidedCategory.braiding P Q)
        (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q)) :
      ∃ βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
          (finiteIntrinsicClosed l E X n).monoidal,
        (∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) ∧
        (∀ n : ℕ, CoefFiniteHomSymmetry
          (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
          (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
        ∀ (n m : ℕ) (h : m ≤ n),
          CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (βet n) (βet m) (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
            (coefFiniteHomProTensor l E X h) ∧
          CoefFiniteHomQuotientCoherence l E X h := by
  classical
  have hn := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finite_tensor_coherence
  change ∀ n : ℕ, ∃ β : @SymmetricCategory (normalizedDVRDerived l E X n) _
      (finiteIntrinsicClosed l E X n).monoidal,
    Nonempty (RingedDerivedTensorCoherence
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) β) at hn
  choose βpro hβpro using hn
  obtain ⟨hsite, hscalar⟩ :=
    finiteHomNormalizedTensorFunctorLaws l E X βet hβet βpro hβpro
  refine ⟨βpro, hβpro, fun n ↦ (hsite n).2, ?_⟩
  intro n m h
  obtain ⟨⟨sF⟩, hβF⟩ := finiteHomEtaleTensorLaws D l _hl E X βet hβet h
  obtain ⟨sG⟩ := (hscalar n m h).1
  obtain ⟨sU⟩ := (hsite n).1
  obtain ⟨sV⟩ := (hsite m).1
  have htensor := finiteHomSiteTensorMateEquations l E X h
  have htower := finiteHomSiteQuotientCoherence l E X h
  have hunit := coefficientMonoidalSquareUnit _ _ _ _ _ _ _ _ _ _ _ _
    (coefFiniteHomSiteIso l E X h) sF sG sU sV htensor
  exact ⟨⟨sF, sG, sU, sV, htensor, hunit⟩,
    hβF, (hscalar n m h).2, htower⟩

end WeilConjectures
