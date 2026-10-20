/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation

/-! # Finite reduction as tensor by a bounded finite-projective sheaf complex

Source: blueprint order 1249, proof steps 1 and 4; Stacks 099M and 091Z.
(blueprint: lem-weil-pbc-completed-finite-quotient-tensor-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Restriction of derived finite reduction is naturally tensor with a bounded
finite-projective sheaf representative of the quotient. The comparison is between
functors, so it transports preservation of the canonical product cones.

Source: blueprint order 1249, proof steps 1 and 4; Stacks 099M and 091Z.
(blueprint: lem-weil-pbc-completed-finite-quotient-tensor-presentation).

Proof: use d.quotientPerfect at n+1 to take a bounded finite-projective A-complex
resolving A/I^(n+1). Exact constant sheafification and flat extension to A_T give
a bounded complex P of finite-free retracts. The completed constant sheaf reduction
identifies its augmentation with the finite quotient sheaf. On a K-flat input, tensor
with this augmentation is a quasi-isomorphism. The ordinary scalar-extension formula
identifies tensor with the quotient with extension followed by restriction. Both
computations commute with chain maps and homotopies. The resolving-class localization
universal property therefore gives the natural isomorphism on all derived objects
and morphisms. Finite-free splittings give the package and preserve the two bounds.
For a zero quotient the zero complex works; no flatness of the quotient is assumed. -/
theorem completedFiniteQuotientTensorPresentation (n : ℕ) :
    ∃ (P : CochainComplex (adicDatumModules T d) ℤ)
      (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
      (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (adicDatumRing T d)) P),
      Nonempty (adicDatumReductionUnderlying T d n ≅
        finiteProjectiveTensorRight T d P hb p) := by
  sorry

end AlgebraicGeometry.Scheme
