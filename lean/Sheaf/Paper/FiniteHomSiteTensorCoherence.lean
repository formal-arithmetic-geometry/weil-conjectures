/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.CoefFiniteHomSiteDescentData

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

Proof: use flat-term K-flat resolutions for each tensor input. Algebra-diagram
pullback/extension coherence for the terminal diagram computes the scalar/site
comparison by balanced scalar association. The scalar-unit equation identifies its
inverse with the fixed restriction mate defining coefFiniteHomSiteIso. The ringed
closed symmetric monoidal construction supplies the intrinsic signed symmetry and
its representative coherence for finiteIntrinsicTensorModels; the prescribed etale
symmetry is its Koszul counterpart. The normalization of each fixed tensorator
identifies it with the corresponding ordinary cochain tensor comparison. Cochain
pullback/tensor coherence proves the associator, both unit, and symmetry equations.
The tensor square is scalar association on pure tensors and its unit sends one to
one. Under successive quotients both composites send (x tensor b) tensor c to the
inverse image of x tensor the product of the images of b and c. Localize these
identities and use the unique normalized tensor comparisons to identify them with
the specified maps. No quotient-flatness or Hom invertibility is needed. -/
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
  sorry

end WeilConjectures
