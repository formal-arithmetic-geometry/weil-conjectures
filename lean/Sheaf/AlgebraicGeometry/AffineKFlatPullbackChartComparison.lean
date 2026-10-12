/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Affine pullback comparison through spectrum charts

Source: Stacks Project, Tags 06Z0 and 08DW.
(blueprint: lem-pc-affine-kflat-pullback-chart-comparison).
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

/-- Transport the affine derived pullback calculation through canonical spectrum charts.
Source: Stacks Project, Tag 08DW(2), using Tag 08DV.
Proof: naturality of toSpecΓ identifies f followed by Y.toSpecΓ with X.toSpecΓ
followed by Spec.map f.appTop. Restriction along these scheme isomorphisms is exact.
Termwise tensor pullback commutes with these restrictions. Tilde of the K-flat module
complex is K-flat; the derived-pullback counits therefore identify both functors with
these termwise calculations. Apply derivedPullback_tilde_iso with the identity resolution
of P and transport its comparison through the chart isomorphisms. Uniqueness of the
localization lift of the exact restriction gives the comparison even when the target
spectrum has an independent localization universe. No quasi-coherence condition on an
arbitrary derived object, or choice of a representative for it, occurs in this statement.
(blueprint: lem-pc-affine-kflat-pullback-chart-comparison). -/
theorem affine_kFlat_pullback_chart_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    (P : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(Y, ⊤)) (.up ℤ)).kFlat P) :
    Nonempty ((derivedPullback f).obj
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (Scheme.Modules.restrictFunctor Y.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor Y.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(Y, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
                (tilde.functor Γ(Y, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P))) ≅
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
