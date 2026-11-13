/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionEvaluationMatePostcompBijective

/-! # Invertibility of the restricted evaluation mate
Source: Stacks Project, Tags 08DJ, 08DL and 08BS.
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

/-- Currying restricted evaluation gives an isomorphism for any natural tensor comparison.
Source: Stacks Project, Tags 08DJ and 08DL; Tag 08BS (exact extension by zero). -/
theorem derivedRestriction_evaluationMate_isIso
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    ∀ (t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L),
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b)) →
      ∀ L E, IsIso ((schemeDerivedTensorHomEquiv U.toScheme
        (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
          ((t (H.obj (op L, E)) L).inv ≫
            R.map (schemeDerivedTensorHomEquiv X (H.obj (op L, E)) L E (𝟙 _)))) :=
  by
    dsimp
    intro t ht L E
    apply isIso_of_yoneda_map_bijective
    intro A
    exact derivedRestriction_evaluationMate_postcomp_bijective X U t ht L E A

end AlgebraicGeometry.Scheme
