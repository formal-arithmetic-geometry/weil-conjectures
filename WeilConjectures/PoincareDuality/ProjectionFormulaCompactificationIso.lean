/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula

/-!
# The exceptional projection morphism with an abstracted pullback identification

`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification` uses the identification
`leftDerivedUpperStarCompactificationIso : Lf^* ≅ Lg^* ⋙ Li^*`. This file restates its defining
formula for an arbitrary isomorphism `e` equal to that identification. Downstream proofs can then
work with a free variable `e`, so they never have to unfold the identification itself.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The defining formula of the exceptional projection morphism, for any isomorphism
`e : Lf^* ≅ Lg^* ⋙ Li^*` equal to `leftDerivedUpperStarCompactificationIso`. -/
lemma exceptionalProjectionMorphismOfCompactification_eq
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (e : L((f)^*⟦Λ⟧) ≅ L((c.g)^*⟦Λ⟧) ⋙ L((c.i)^*⟦Λ⟧))
    (he : e = leftDerivedUpperStarCompactificationIso Λ c) :
    exceptionalProjectionMorphismOfCompactification Λ c K B =
      (derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism
          ((D((c.i)_!open⟦Λ⟧)).obj K) B ≫
        (R((c.g)_*⟦Λ⟧)).map
          (@inv _ _ _ _ ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i
              ).projectionComparison K ((L((c.g)^*⟦Λ⟧)).obj B))
            (isIso_openImmersionProjectionComparison Λ c.i K ((L((c.g)^*⟦Λ⟧)).obj B)) ≫
            (D((c.i)_!open⟦Λ⟧)).map (K ◁ e.inv.app B)) := by
  subst he
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
