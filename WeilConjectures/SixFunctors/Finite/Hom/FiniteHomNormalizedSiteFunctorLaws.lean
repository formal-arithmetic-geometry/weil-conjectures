/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedSiteStrong
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedSiteSymmetry

/-! # Normalized finite-Hom site comparison laws

This is the site-comparison half of the normalized tensor-functor law. -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The normalized inverse-image comparison is strong and signed at every finite level.

Source: the first independent obstruction in the normalized finite-Hom proof.
The core monoidal construction and the signed descent are stated separately in
`finiteHomNormalizedSiteStrong` and `finiteHomNormalizedSiteSymmetry`; this
constructor combines them for each finite level. Their K-flat representative
proofs use `finiteHomNuTensor_existsUnique`, the intrinsic tensor coherence and
`hβet`, while the target statement itself remains unchanged. -/
theorem finiteHomNormalizedSiteFunctorLaws
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
    ∀ n : ℕ,
      Nonempty (CoefFiniteHomStrong
        (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
        (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
      CoefFiniteHomSymmetry
        (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
        (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n) := by
  intro n
  obtain ⟨s, hs⟩ := finiteHomNormalizedSiteStrong l E X n
  refine ⟨⟨⟨s, hs⟩⟩, ?_⟩
  exact finiteHomNormalizedSiteSymmetry l E X n (βet n) (hβet n) (βpro n)
    (hβpro n) s hs

end WeilConjectures
