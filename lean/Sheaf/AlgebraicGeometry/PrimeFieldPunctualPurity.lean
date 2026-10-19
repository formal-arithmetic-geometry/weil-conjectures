/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity

import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.ExcellentRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import Sheaf.Paper.NoetherianPrimePowerSmoothDuality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest
import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
import Sheaf.RingTheory.PrimeFieldCompleteCoordinateModel

/-!
# Punctual purity over prime fields

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2 and Proposition 3.2.5, pp.244--245
(blueprint: lem-per-prime-field-punctual-purity).

Punctual purity and its canonical level-one Kummer class are the published definitions
of `Sheaf.AlgebraicGeometry.PunctualPurity`. This module states only the prime-field theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- Every regular Noetherian scheme over a prime field is punctually pure for invertible
prime coefficients. Source: ILO XVI Proposition 3.2.5, p.245
(blueprint: lem-per-prime-field-punctual-purity).

Proof:
1. Fix w and R = O_{X,w}. The punctual strict-completion test reduces to the complete
   strictly henselian regular local ring B = completion(R^sh), of the same dimension d.
   The prime field still embeds into B, since a unital map from a field to B is injective.
2. The prime-field complete-coordinate model gives B = completion(F[T_1,...,T_d]) at
   (T_1,...,T_d), with F the residue field. The pullback of the zero section of A^d_F is
   the closed point of Spec B, with residue map the identity.
3. F and its polynomial algebra are excellent. The G-ring completion theorem makes
   Spec B → A^d_F regular: flat with geometrically regular Noetherian fibres. Excellence
   is used only for this polynomial algebra, never for R.
4. Affine-space smoothness and its projective compactification allow prime-power smooth
   duality at n=1. The mixed smooth-Gysin section identity says the Kummer class of the
   zero section is inverse to the shifted smooth orientation, hence is invertible.
5. Closed compact-support direct image is exact closed direct image; uniqueness of right
   adjoints identifies its adjoint with closedSupportPlus compatibly with the counit.
   Regular supported base change and flat compatibility of the class calculus carry the
   zero-section class to exactly the normalized closed-point class of B, with twist d
   and shift 2d. This class is consequently invertible.
6. The strict-completion equivalence returns purity to R. Varying w proves the assertion.
   Empty X is vacuous; d=0 uses empty coordinate tuples and identity class maps.
The cited nodes are respectively lem-per-punctual-strict-completion-test,
lem-per-prime-field-complete-coordinate-model, lem-exc-fields-excellent,
lem-exc-finite-type-localization-excellent, lem-weil-pbc-g-ring-completion-regular,
lem-weil-pbc-geometrically-regular-finitely-generated-extensions,
sbc-lem-affine-space-smooth, lemma-nagata-relative-affine-space-open-immersion,
lemma-nagata-projective-space-base-change-proper, lem-per-regular-lci-geometric-calculus,
lem-per-noetherian-prime-power-smooth-duality, lem-per-smooth-gysin-mixed-identities,
lem-per-regular-supported-base-change and lem-per-regular-immersion-class-calculus. -/
theorem primeField_punctuallyPure (ℓ : ℕ) (hℓ : ℓ.Prime) (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* ℚ) ∨ ∃ p : ℕ, p.Prime ∧ Nonempty (k ≃+* ZMod p))
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X]
    (_hX : IsRegularScheme X) (_hℓX : IsUnit (ℓ : Γ(X, ⊤))) :
    IsPunctuallyPure ℓ hℓ X := by
  sorry

end AlgebraicGeometry.Etale
