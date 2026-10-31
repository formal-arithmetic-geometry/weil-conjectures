/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingAdjunctionData.IntegralDualizingAdjunctionData

/-! # The exceptional value has the prescribed finite-dualizing presentation

Source: current blueprint prop-coef-integral-dualizing.proof.md, first paragraph.
(blueprint: lem-coef-integral-dualizing-exceptional-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The constructible exceptional value has a complete coherent finite-dualizing
presentation for the prescribed finite-dualizing data. This statement asserts neither
an enriched mapping-complex comparison nor the Tor bound.

Source: current blueprint prop-coef-integral-dualizing.proof.md, first paragraph
(blueprint: lem-coef-integral-dualizing-exceptional-presentation).

Proof: the coefficient unit has the one-term free scalar model. Apply the constructible
exceptional-adjoint existence theorem over the pulled-back condensed integer ring to the
structure morphism. The integral section-action equivalence and the integral constructibility
criterion identify its source and target with the two sfIntegralConstructible categories.
The compact-support realization comparison identifies its left adjoint with the published
strict compact-support reduction functor followed by total derived limit. Transporting the
adjunction gives the support, right and adjunction fields; transport of the coefficient unit
gives unit and unitIso. Its support comparison is the natural realization isomorphism, with
all maps, not just objectwise comparisons.

Scalar exceptional comparison for R to A_n identifies the reductions of the exceptional
value with the condensed finite exceptional values. The finite condensed agreement theorem
identifies those values with integralDualizingFiniteTerm, with their counits. The quotient
mate composition identity makes these identifications commute with every transition.
Integral-model completeness gives the canonical Roos triangle for the exceptional value.
The isomorphisms e and their coherence he identify its reduction tower with T. Conjugating
the two product maps by the product of these level isomorphisms transports the canonical
triangle to the actual restricted evaluations of T.
The scalar-adjunction identities identify its projection adjuncts with the finite comparison
isomorphisms and give their coherence. This is the required limit presentation. No equality
of arrows is deduced merely from equality of their reductions. For empty X both values are
zero; at the coefficient point this is the identity adjunction and the regular module.
The index n means exponent n+1, including the residue quotient n=0.
-/
theorem integralDualizing_exceptional_presentation
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    : ∃ A : IntegralDualizingAdjunctionData D l hl E X,
      IntegralDualizingLimitPresentation l E D hl X T (A.right.obj A.unit).obj := by sorry

end WeilConjectures
