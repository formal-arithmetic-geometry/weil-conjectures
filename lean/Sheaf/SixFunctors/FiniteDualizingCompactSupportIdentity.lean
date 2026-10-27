/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! Compact-support normalization at an identity finite coefficient quotient. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The compact-support coefficient comparison for an identity quotient is the
normalized scalar unit at the output followed by the image of the inverse unit.
This is the first mate-pasting step in the proof of
`finiteDualizing_compact_normalization`.  Expand the fixed compactification as
proper direct image after extension by zero, identify both factors with their
canonical scalar mates, and apply the identity triangle for the scalar
adjunction.  Naturality of the open balancing map and of the proper scalar mate
then gives the displayed equality for every derived etale object, including
zero objects and non-flat coefficient presentations.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`, paragraphs 1--3.
(blueprint: lem-coef-dualizing-compact-normalization)
-/
theorem finiteDualizing_compact_support_identity :
    ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X),
      Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E
          (le_refl n)) (finiteDualizingCompactification D X) K =
        (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
          (finiteDualizingQuotient_id l E n)).hom.app
            ((finiteDualizingEtaleSupport l E D X n).obj K) ≫
        (finiteDualizingEtaleSupport l E D X n).map
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
            (finiteDualizingQuotient_id l E n)).inv.app K) := by
  sorry

end WeilConjectures
