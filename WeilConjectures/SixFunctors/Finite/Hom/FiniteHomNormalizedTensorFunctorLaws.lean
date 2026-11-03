/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedSiteFunctorLaws
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedQuotientFunctorLaws

/-! # Functor laws for normalized finite coefficient tensors

Source: blueprint finite Hom proof, normalized scalar and site tensor comparisons.
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

/-- The separately normalized site and quotient tensor functors are strong and
preserve the signed symmetry. No scalar/site natural transformation is asserted.
Source: blueprint thm-coef-finite-hom proof, final paragraph; the ordinary signed
pullback and scalar-extension tensor formulas
(blueprint: lem-coef-finite-hom-normalized-tensor-functor-laws).

Proof: for each input choose a flat-term K-flat resolution. The normalization
of finiteHomNuTensor identifies its value on these resolutions with the ordinary
inverse-image tensor comparison. The quotient calculus tensor_model field does
the same for its specified derived scalar-extension tensorator. In each case
scalar association on pure tensors preserves reassociation, sends the scalar unit
to the scalar unit, and commutes with the signed swap: the coefficient ring maps
have degree zero, so the sign is unchanged. The intrinsic coherence hypotheses
identify these ordinary constraints with the prescribed intrinsic ones; hβet does
the same on the etale side. Localize the associator, both unit and swap equations,
and transport them along the resolution isomorphisms. The inverse tensorator and
localized unit give CoreMonoidal; its tensorator is the specified inverse by the
normalization uniqueness. The two swap equations give the displayed symmetry
laws. Identity quotients, the first positive exponent, zero complexes and the
empty scheme use the same formulas. No quotient flatness, geometric finiteness
or internal Hom invertibility enters this construction. -/
theorem finiteHomNormalizedTensorFunctorLaws
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
      (finiteHomEtaleClosed l E X n).monoidal)
    (hβet : ∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
      HEq ((βet n).toBraidedCategory.braiding P Q)
        (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q))
    (βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
      (finiteIntrinsicClosed l E X n).monoidal)
    (hβpro : ∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) :
    (∀ n : ℕ,
      Nonempty (CoefFiniteHomStrong
        (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
        (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
      CoefFiniteHomSymmetry
        (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
        (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
    ∀ (n m : ℕ) (h : m ≤ n),
      Nonempty (CoefFiniteHomStrong
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)) ∧
      CoefFiniteHomSymmetry
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
        (coefFiniteHomProTensor l E X h) := by
  constructor
  · exact finiteHomNormalizedSiteFunctorLaws l E X βet hβet βpro hβpro
  · exact finiteHomNormalizedQuotientFunctorLaws l E X βpro hβpro

end WeilConjectures
