/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSupportSystemHom
public import Sheaf.SixFunctors.IntegralDualizingMappingTower

/-! # Compact support reconstructed before applying Hom

Source: prop-coef-integral-dualizing, proof paragraph 2, compact-support reduction.
(blueprint: lem-coef-integral-dualizing-support-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The actual integral support value is constructible and its reduction is the
quotient-system support value, naturally before any dual or Hom is taken.

Source: prop-coef-integral-dualizing, second proof paragraph, compact-support
reduction; integralCompactSupport_prescribedReductions.
(blueprint: lem-coef-integral-dualizing-support-reduction).

Proof: fix the Nagata compactification used by both support constructions.
The normalized reduction calculus compares S.reduction with the reduction used
in integralDualizingCompactTower by the unique left-adjoint comparison compatible
with their total-limit adjunctions. The scalar restriction isomorphisms of G
identify its ordinary open and proper operations with the actual ones on towers.
An R-linear map between the quotient-sheaf modules is quotient-linear: locally
every quotient scalar lifts to R, so R-linearity gives the required scalar law.
Thus the ordinary comparisons lift to quotient modules before being derived;
their derived comparisons retain the ordinary adjunction units and counits.
Compose these comparisons on strict representatives to identify the restricted
system support with the compact-support tower in the definition of F. The
right-derived-limit comparison therefore identifies F with the total limit of
that system, retaining each of its actual projections.
For each constructible K, integral_residue_tor gives a common finite Tor interval
for its reductions. A finite dimension bound exists since X is finite type over
a field. Apply integralCompactSupport_prescribedReductions to the defining Roos
triangle and these bounds. It proves that F(K) is integral constructible and
that every projection's reduction adjunct is invertible. Take the reduction
counit for the base calculus B and transport it through the strict tower
comparison just constructed. Its evaluated components are precisely those
projection adjuncts, by B.counit_projection. B.isIso_iff_evaluations makes the
counit invertible as a system map. Naturality of the counit, strict support
comparisons and limit comparison gives a natural isomorphism of functors.
This argument constructs the system map before testing its evaluations; it
does not lift a family of finite isomorphisms. Zero input and empty X give zero
support, and the first quotient is included in the same Roos triangle. -/
theorem integralDualizing_support_reduction
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (B : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))) :
    let F := (sfIntegralConstructible l E X).ι ⋙
      integralDualizingCompactTower l E D hl X ⋙
        integralDualizingLimit l E (Spec (.of D.k))
    (∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E (Spec (.of D.k)) (F.obj K)) ∧
      Nonempty (F ⋙ B.reduction ≅ integralDualizingSystemSupport D l E X S G) := by sorry

end WeilConjectures
