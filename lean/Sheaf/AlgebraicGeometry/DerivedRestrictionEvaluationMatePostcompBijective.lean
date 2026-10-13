/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048

/-- The explicit restricted evaluation mate induces bijections on all Hom sets.
Source: Stacks Project, Tags 08DJ, 08DL and 08BS.
(blueprint: lem-sc-derived-restriction-evaluation-mate-postcomp-bijective).

Proof: use extension by zero as the left adjoint to restriction. The unit is an
isomorphism, and tensoring an object in the essential image of extension by zero
with an arbitrary complex remains in that image by the stalkwise K-flat tensor
calculation. Transpose a map along the adjunction and the canonical tensor-Hom
equivalences. Naturality of the supplied tensor comparison identifies the resulting
map with postcomposition by the displayed mate. Every operation in this composite
is a bijection, proving the assertion.
-/
theorem derivedRestriction_evaluationMate_postcomp_bijective
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
      ∀ L E, ∀ A : schemeDerivedCategory U.toScheme,
        Function.Bijective (fun f : A ⟶ R.obj (H.obj (op L, E)) ↦
          f ≫ (schemeDerivedTensorHomEquiv U.toScheme
            (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
            ((t (H.obj (op L, E)) L).inv ≫
              R.map (schemeDerivedTensorHomEquiv X
                (H.obj (op L, E)) L E (𝟙 _)))) := by
  sorry

end AlgebraicGeometry.Scheme
