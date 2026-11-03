/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenPastingData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange

/-! The normalized proper/open mate on arbitrary finite-type compactification squares.
Source: the mate and clopen-localization steps of
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

/-- Existence, normalization, and pointwise uniqueness of the proper/open mate.
The proof forms the clopen lift of the open square, identifies its restriction with the
proper compositor, and takes the open-adjunction transpose. Naturality is obtained by the
adjunction hom bijection; no separatedness over the coefficient field is used.
Source: Steps 1--3 of the proof of `lem-sf-condensed-proper-open-interchange`.
(blueprint: lem-sf-condensed-proper-open-interchange) -/
theorem condensedProperOpenInterchangeNormalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [IsProper p] (data : CondensedOpenProper.Pasting Λ) :
    ∃ δ : (moduleObjectDerivedPushforward Λ p ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory) ⟶
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        moduleObjectDerivedPushforward Λ c.obj.obj.g),
      ∀ A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        compositionInterchangeIsNormalized Λ p i c A (δ.app A) ∧
        (∀ m, compositionInterchangeIsNormalized Λ p i c A m → m = δ.app A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
