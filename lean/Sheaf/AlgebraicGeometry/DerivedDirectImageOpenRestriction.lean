/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Derived direct image commutes with restriction to an open

Source: Stacks Project, Cohomology, Lemma 20.32.4, Tag 08FE
(blueprint: lem-pc-restrict-derived-direct-image-open).
-/

@[expose] public section

universe u wX wY wU wV

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option synthInstance.maxHeartbeats 100000 in
-- The explicit additivity witnesses require a larger typeclass-search budget.
/-- Restricting `Rf_*` to an open `V` is naturally isomorphic to first restricting to
`f ⁻¹ᵁ V` and then applying the derived direct image of the induced morphism `f ∣_ V`.
The components of this functor isomorphism are the canonical comparisons for every E.
Source: Stacks Project, Cohomology, Lemma 20.32.4 (Tag 08FE)
(blueprint: lem-pc-restrict-derived-direct-image-open).

Proof:
1. Choose a K-injective resolution E → I on X. Its restriction to the inverse-image
   open is K-injective by `lem-sc-derived-k-injective-restrict-open` (Tag 08BS).
2. By `def-pc-ringed-spaces-derived-direct-image`, `Rf_*E` is represented by f_*I,
   and the derived direct image of the restricted E is represented by g_*(I|U).
   On every open W of V both complexes have sections I(f⁻¹W). These identifications
   commute with differentials and are natural in E, giving the natural isomorphism. -/
theorem schemeDerivedDirectImage_openRestriction {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty
      ((schemeDerivedDirectImage f ⋙
          (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
              (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv V))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _))) ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
              (D := SheafOfModules.{u}
                (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (f ⁻¹ᵁ V)))
          (Functor.additive_of_preserves_binary_products _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)) ⋙
          schemeDerivedDirectImage (f ∣_ V)) := by
  sorry

end AlgebraicGeometry
