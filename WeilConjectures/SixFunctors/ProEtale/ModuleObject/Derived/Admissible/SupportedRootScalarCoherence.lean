/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.SignedDivisorScalarComparisons

/-! # Coherence of the supported coefficient and root comparisons

Source: signed divisor coefficient-change proof Steps 1 and 6.
(blueprint: lem-pur-supported-root-scalar-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible
variable (P : WeilConjectures.PurityFiniteSetting.{u})
variable {Λ Λ' Λ'' : ScalarSixRing.{u}}

/-- Formal supported-source and shifted-root coherence, without any divisor class.
Source: closed projection and the normalized scalar mates, signed divisor proof
Steps 1 and 6 (blueprint: lem-pur-supported-root-scalar-coherence).
Proof: on the open complement the supported coefficient module is zero; on D
its pullback is the regular coefficient module. Exact strong monoidal pullbacks
jointly detect flatness and invertibility. Thus i_*Lambda_D is flat and ordinary
scalar extension of it is i_*Lambda'_D. The ordinary comparison is the adjunct
of divisorSourceUnit: the closed counit and the restriction/direct-image
comparison have identity underlying maps, so its unit sends supported one to
one. Compute the derived adjunct on this flat single complex. The normalized
scalar/pullback comparison and the geometric adjunction triangle identify it
with the displayed scalarDirectImageMate composite, including nonflat maps.
For composition, transpose through the composite scalar adjunction. The
conjugate definition of scalarSixTower turns both transposes into the same
composite semilinear map. The source maps compose by divisorSourceUnit_comp;
the root maps compose by divisorRootMap_comp. The canonical shift comparison
is the unique comparison compatible with the exact restriction functor, so
this same transposition argument works after shift by two. For identity maps,
the semilinear source and root maps are identities by divisorSourceUnit_id and
divisorRootMap_id. Their transposes are exactly the conjugate identity
comparison defining divisorScalarIdentity. None of these arguments mentions a
Cartier, frame, Kummer, Chern, Thom or purity class; empty support is included. -/
theorem supportedRootScalarCoherence
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') {D X : Scheme.{u}} [IsLocallyNoetherian X]
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    (i : D ⟶ X) [IsClosedImmersion i] :
    IsIso (divisorScalarSource a i) ∧
    (divisorScalarSource a i =
      (scalarSixChange a X).map (divisorClosedIso Λ i).inv ≫
        (scalarDirectImageMate a i).app _ ≫
        (RootCoordinateFace.lower Λ'.X i).map (divisorScalarUnit a D) ≫
        (divisorClosedIso Λ' i).hom) ∧
    (∀ (hΛ'' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ''))
      (a' : Λ' ⟶ Λ''),
      (scalarSixTower a a' X).hom.app _ ≫ divisorScalarSource (a ≫ a') i =
        (scalarSixChange a' X).map (divisorScalarSource a i) ≫ divisorScalarSource a' i ∧
      (scalarSixTower a a' X).hom.app _ ≫ divisorScalarTarget P hΛ hΛ'' (a ≫ a') X =
        (scalarSixChange a' X).map (divisorScalarTarget P hΛ hΛ' a X) ≫
          divisorScalarTarget P hΛ' hΛ'' a' X) ∧
    (divisorScalarSource (𝟙 Λ) i = (divisorScalarIdentity Λ X).hom.app _) ∧
    (divisorScalarTarget P hΛ hΛ (𝟙 Λ) X = (divisorScalarIdentity Λ X).hom.app _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
