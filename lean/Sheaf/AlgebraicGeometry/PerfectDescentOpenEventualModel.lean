/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Eventual perfect model on a specified open

Source: Stacks Project, Tag 09RF, descent of each restriction and enlargement of its stage.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Descent on one original open supplies models on its inverse image at every later stage.
Source: Stacks Project, Tag 09RF, choice and subsequent base change of each local model.
(blueprint: lem-pc-perfect-descent-open-eventual-model).

Proof: Put O = f inverse W and restrict the limit perfect object to the inverse image of O.
The presentation O.toScheme → Xi is an open immersion with image W, because W is contained
in the image of f. Pullback along the open immersion preserves perfectness (Tag 09UA).
Apply dW to this presentation. It gives an index j ≥ i, a perfect stage model, and a limit
comparison. For k ≥ j pull that model back along the transition morphism. The canonical
cartesian identifications of the base change of O with the inverse-image open in the base
change of Z transport it to A. Pullback preserves perfectness; the composition comparison
for derived pullbacks and the comparison with exact open restriction identify its limit
pullback with the displayed restriction of E. Empty opens and non-antisymmetric preorders
use the same pullback identifications; no colimit hypothesis is needed. -/
theorem perfect_descent_open_eventual_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W : Xi.Opens) (dW : PerfectDescentOnOpen R c i Xi s W)
    (Z : Scheme.{u}) (f : Z ⟶ Xi) [IsOpenImmersion f] (hW : W ≤ f.opensRange)
    (E : schemeDerivedCategory (pullback (f ≫ s) (Spec.map (c.ι.app i))))
    (hE : (pullback (f ≫ s) (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      let X := pullback (f ≫ s) (Spec.map (c.ι.app i))
      let g := baseChangeMap (f ≫ s)
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let U := (pullback.fst (f ≫ s)
        (Spec.map (R.map (homOfLE (hij.trans hjk)))) ≫ f) ⁻¹ᵁ W
      ∃ A : schemeDerivedCategory U.toScheme, U.toScheme.IsPerfect A ∧
        Nonempty ((derivedPullback (g ∣_ U)).obj A ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) := by sorry

end AlgebraicGeometry
