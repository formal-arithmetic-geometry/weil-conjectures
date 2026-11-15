/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Ambient etale adjunction and projection for a supplied compactification

proof.md`, paragraph 1;
Stacks Project, Tags 0F0G, 0GL1 and 0F5Y
.

The factorization is supplied explicitly as `Compactification f`, which does not
require its open immersion to be quasi-compact. The categories are ordinary and
unbounded. The inverse image appearing in the projection map is canonically the
termwise exact inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`.

## Main declarations

* `sfEtaleAmbientAdjointProjection`: the right adjoint exists and every canonical
  projection component is invertible.
* `sfEtaleAmbientTensorMap`: its counit transpose for any selected right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The ordinary unbounded compact-support functor of a supplied open/proper
factorization has a right adjoint, and its canonical projection map is invertible.
proof.md`, paragraph 1;
Stacks Project, Tags 0F0G, 0GL1 and 0F5Y. -/
theorem sfEtaleAmbientAdjointProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint ∧
      ∀ (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y),
        IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K) := by
  have hAdj :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint := by
    have := isLeftAdjoint_proper_rightDerivedLowerStar A c.g
    have := (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) c.i).isLeftAdjoint
    change (D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((c.g)_*[ModuleCat.{u + 1} A])).IsLeftAdjoint
    infer_instance
  refine ⟨hAdj, ?_⟩
  intro M K
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  rw [projectionMapOfCompactification_app_app]
  infer_instance

/-- The morphism theta for a selected right adjoint G, with omega = G(A_Y).
It is the transpose of inverse projection, followed by the counit tensored with
K and the left unit constraint. The adjunction is data selecting the right
adjoint whose existence is sfEtaleAmbientAdjointProjection, not an additional
geometric hypothesis. No invertibility assertion is made about theta.
proof.md`, paragraph 1. -/
noncomputable def sfEtaleAmbientTensorMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj (G.obj (constantComplex A Y))).obj
      ((L(upperStar (ModuleCat.{u + 1} A) f)).obj K) ⟶ G.obj K :=
  letI := (sfEtaleAmbientAdjointProjection A c).2 (G.obj (constantComplex A Y)) K
  adj.homEquiv _ _
    (inv (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      (G.obj (constantComplex A Y))).app K) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (adj.counit.app (constantComplex A Y))).app K ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom)

end AlgebraicGeometry.Etale
