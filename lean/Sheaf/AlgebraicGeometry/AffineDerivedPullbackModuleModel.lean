/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # A module-complex model for affine derived pullback

Source: Stacks Project, Tag 08DW(2), using Tag 06Z0 and Tag 08DV.
(blueprint: lem-pc-affine-derived-pullback-module-model).
-/

@[expose] public section

universe u w wS

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Affine derived pullback has a module-complex representative on the target spectrum.
Source: Stacks Project, Tag 08DW(2), Tag 06Z0 and Tag 08DV.
Proof: use the canonical spectrum presentations of X and Y and the induced ring map.
The affine derived equivalence represents E by termwise tilde of a module complex M.
Choose a K-flat resolution P of M. The affine pullback comparison identifies its
pullback with termwise tilde of the base-changed complex B tensor P. The tilde complex of P,
restricted along Y to its spectrum, represents E.
The base-changed complex along f.appTop.hom represents its pullback after termwise tilde
and exact restriction along X to its spectrum. Transport the natural comparisons
through the two canonical spectrum presentations. No flatness of f or boundedness of E is
needed; the zero ring is allowed.
(blueprint: lem-pc-affine-derived-pullback-module-model). -/
theorem exists_affine_derivedPullback_module_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E) :
    ∃ P : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(Y, ⊤)) (.up ℤ)).kFlat P ∧
      Nonempty (E ≅ DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (Scheme.Modules.restrictFunctor Y.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor Y.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(Y, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
                (tilde.functor Γ(Y, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P))) ∧
      Nonempty ((derivedPullback f).obj E ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).Additive; infer_instance)
          (by change PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
              infer_instance)
          (by change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
              infer_instance)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
                (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                  SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                  (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                  (((ModuleCat.extendScalars f.appTop.hom).mapHomologicalComplex
                    (.up ℤ)).obj P)))) := by
  sorry

end AlgebraicGeometry
