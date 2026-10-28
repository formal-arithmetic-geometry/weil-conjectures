module
public import Sheaf.Paper.PullbackIdentitiesScalarExtension
import Sheaf.Paper.IntegralInverseImageComparisonComposition

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Precomposition identity for inverse cancellation.

Source: the Weil-structures paragraph, parent node steps 4--6.
(blueprint: lem-sf-integral-automorphism-cancellation-precomposition).

Proof: expand the specified epsilon into the inverse kappa factors and ordinary
counit, apply the actual kappa composition law, transport across the inverse
identity, and use the normalized identity unit. This is the strictly simpler
precomposed equality; the parent theorem cancels its invertible precomposition. -/
theorem integralAutomorphismCancellation_precomposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : X ⟶ Y) [IsIso g] (K : sfIntegralConstructibleCategory l E Y) :
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
    HEq (A ≫ (pullbackIdentityEpsilon l E g K).hom)
      (A ≫ ((integralComparisonComposition l E C (inv g) g K).symm ≪≫
        eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonUnit l E C Y K).hom) := by
  sorry

end WeilConjectures
