/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension
import WeilConjectures.SmoothPurity.Integral.IntegralAutomorphismCancellationPrecomposition

/-! # Normalization of integral inverse cancellation

Source: the Weil-structures paragraph of the open-closed triangle proof, canonical
inverse-composition comparisons, expanded by the parent node's steps 4--6.
(blueprint: lem-sf-integral-automorphism-cancellation-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The counit-built completed compositor and unit give the same cancellation as
ordinary inverse image, transported through the actual completion comparison.
HEq retains the standard integral and scalar-reduction category presentations;
the compositor composite uses the full constructible inclusion's presentation.

Source: the Weil-structures paragraph, canonical inverse-composition comparison;
parent node steps 4--6, using the whole-system normalization of Stacks 099N(5).
(blueprint: lem-sf-integral-automorphism-cancellation-normalization).

Proof: take a flat-term K-flat representative P of K and its simultaneous quotient
system. Reindex this system successively by g and its inverse. The coefficient
isomorphisms compose to the identity on every quotient, including all transition
maps and the augmentation. Thus the specified system compositor followed by its
identity unit is the sectionwise inverse-image counit on this whole system.
Realize by the total-limit functor. The representative normalization of the two
pullback realization maps identifies the counit-built compositor with this
realized system map. The normalization of the ordinary-to-completed comparison
identifies its composite with the realization with inverse image of the actual
reconstruction unit. Substitute this equation for g and its inverse. Naturality
of the reconstruction unit and the adjunction triangle identity cancel the two
intermediate reduction/limit counits. The remaining factors are lambda for the
inverse, inverse image of lambda for g, and the inverse-image counit, precisely
pullbackIdentityEpsilon. This calculation is on entire systems before total
limit; it does not assume that individual finite reductions detect morphisms.
Naturality and the resolving localization transport the equality from P to K.
The argument includes the identity automorphism, where it is the adjunction
triangle identity, and the zero object, where both maps are the unique map. -/
theorem integralAutomorphismCancellation_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : X ⟶ Y) [IsIso g] (K : sfIntegralConstructibleCategory l E Y) :
    HEq (pullbackIdentityEpsilon l E g K).hom
      (((integralComparisonComposition l E C (inv g) g K).symm ≪≫
        eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonUnit l E C Y K :
        ((constructibleIntegralPullback l E g ⋙
          constructibleIntegralPullback l E (inv g)).obj K).obj ≅ K.obj).hom) := by
  apply heq_of_eq
  let hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := fun x ↦
    isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
      ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
        isUnit_of_invertible (l : X.residueField x))
  let hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := fun y ↦
    isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
      ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
        isUnit_of_invertible (l : Y.residueField y))
  let A := (inverseImageIntegralDerived l E (inv g)).map
    (inverseImagePullbackComparisonDerived l E g hX hY K.obj) ≫
    inverseImagePullbackComparisonDerived l E (inv g) hY hX
      ((constructibleIntegralPullback l E g).obj K).obj
  haveI : IsIso (inverseImagePullbackComparisonDerived l E g hX hY K.obj) :=
    pullbackIdentityKappa_isIso l E g hX hY K
  haveI : IsIso (inverseImagePullbackComparisonDerived l E (inv g) hY hX
      ((constructibleIntegralPullback l E g).obj K).obj) :=
    pullbackIdentityKappa_isIso l E (inv g) hY hX ((constructibleIntegralPullback l E g).obj K)
  apply (cancel_epi A).1
  have h := integralAutomorphismCancellation_precomposition l E C g K
  dsimp only [A, hX, hY] at h
  exact eq_of_heq h


end WeilConjectures
