/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData

/-! # Signed descent for the normalized finite-Hom site comparison

This is the signed-symmetry half of the normalized site comparison law.
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

/-- A normalized core monoidal structure commutes with the prescribed signed
site braidings.

Source: the signed-swap paragraph of the finite-Hom site-comparison proof
(blueprint: lem-coef-finite-hom-normalized-site-symmetry). On simultaneous
K-flat representatives, the ordinary comparison sends the Koszul swap to the
intrinsic signed swap. The representative square for `finiteHomNuTensor` and
the supplied intrinsic tensor coherence transport this equation through
localization. This statement supplies the core and its normalization as input
and proves only the remaining signed compatibility. -/
theorem finiteHomNormalizedSiteSymmetry
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    (βet : @SymmetricCategory (finiteHomEtale l E X n) _
      (finiteHomEtaleClosed l E X n).monoidal)
    (hβet : ∀ (P Q : finiteHomEtale l E X n),
      HEq (βet.toBraidedCategory.braiding P Q)
        (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q))
    (βpro : @SymmetricCategory (normalizedDVRDerived l E X n) _
      (finiteIntrinsicClosed l E X n).monoidal)
    (hβpro : Nonempty (RingedDerivedTensorCoherence
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) βpro))
    (s : @Functor.CoreMonoidal _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
      (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n))
    (hs : ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
        (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n) s P Q) =
        ((finiteHomNuTensor l E X n).app (P, Q)).symm) :
    CoefFiniteHomSymmetry
      (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
      βet βpro (finiteHomNu l E X n) (finiteHomNuTensor l E X n) := by
  sorry

end WeilConjectures
