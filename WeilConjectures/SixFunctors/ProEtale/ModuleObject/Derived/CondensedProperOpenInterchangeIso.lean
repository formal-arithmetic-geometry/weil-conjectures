/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchangeNormalized

/-! Constructible finite-Tor invertibility of the normalized proper/open mate.
Source: the affine-chart boundary-vanishing and open-closed detection steps of
`lem-sf-condensed-proper-open-interchange`.
(blueprint: lem-sf-condensed-proper-open-interchange)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The normalized mate is invertible on bounded constructible finite-Tor inputs.
The proof restricts to affine target charts, applies proper/open boundary vanishing to the
clopen lift, and detects the resulting counit isomorphism by the ringed open-closed sequence.
Source: Steps 4--8 of the proof of `lem-sf-condensed-proper-open-interchange`.
(blueprint: lem-sf-condensed-proper-open-interchange) -/
theorem condensedProperOpenInterchangeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [IsProper p] (data : CondensedOpenProper.Pasting Λ)
    (δ : (moduleObjectDerivedPushforward Λ p ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory) ⟶
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        moduleObjectDerivedPushforward Λ c.obj.obj.g))
    (hδ : ∀ A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
      compositionInterchangeIsNormalized Λ p i c A (δ.app A)) :
    ∀ A, (constantModelBoundedConstructible Λ X A ∧
      DerivedCategory.finiteTorAmplitude _ A) → IsIso (δ.app A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
