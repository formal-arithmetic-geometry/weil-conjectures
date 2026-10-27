/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.SixFunctors.CompactSupportProperImageTower

/-! # Pasting the normalized direct-image coefficient squares -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The normalized direct-image restriction squares respect successive restriction.
This is independent of a completed input K and of the coefficient reduction map.
Source: Stacks Tags 0D6E and 0D6J.
(blueprint: lem-sf-direct-image-restriction-pasting).
Proof: the underived completed/finite and finite/finite restriction squares preserve
sections by sfDirectImageRestrictionComparison_existsUnique and d.sections. Their
pastes are consequently equal after inserting the restriction compositors. Resolve a
finite-coefficient complex by a K-injective complex, and resolve every restricted
complex once more. Apply d.normalization and the resolution characterization of
sfDerivedRestrictionComparison to the two pastes. The common ordinary paste gives
equal derived maps on these models. Cancel the resolution quasi-isomorphisms and
extend by naturality to B. This never assumes restriction preserves K-injectives. -/
theorem sfDirectImageRestriction_pasting
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ)
    (B : normalizedDVRDerived l E X n) :
    (sfDerivedRestrictionComparison l E p (n + 1)).hom.app
          ((normalizedDVRRes l E X (Nat.le_succ n)).obj B) ≫
        (coefficientFiniteDerivedRestriction l E Y (n + 1)).map
          ((d.comparison n).hom.app B) ≫
        (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app
          ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj B) =
      (sfCompletedDerivedDirectImage l E p).map
          ((compactSupportSystemRestrictionComp l E X (Nat.le_succ n)).hom.app B) ≫
        (sfDerivedRestrictionComparison l E p n).hom.app B := by
  sorry

end WeilConjectures
