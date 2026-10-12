/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Derived tensor through the canonical affine spectrum chart

Source: Stacks Project, Tags 08DX(2) and 08DV.
(blueprint: lem-pc-affine-derived-tensor-chart-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Compute affine derived tensor through the canonical spectrum chart, on given
module complexes and a given K-flat resolution of the first complex.
Source: Stacks Project, Tag 08DX(2), using Tag 08DV.
Proof: X.toSpecΓ is an isomorphism because X is affine. Exact restriction along it
preserves quasi-isomorphisms, tensor products, coproducts, and K-flat complexes.
Termwise tilde sends the given quasi-isomorphism s to a quasi-isomorphism, and tilde P
is K-flat by Tag 08DV. Thus restriction of tilde P is a K-flat representative of
restriction of tilde M. Compute the left derived tensor using that representative.
The affine tilde total-tensor comparison, restricted degree by degree, identifies
its total tensor with restriction of tilde Tot(P tensor N). Restriction preserves
arbitrary coproducts, including those in the unbounded total complex. This proves
the comparison for the specified resolution, without choosing an arbitrary derived
model. No quasi-coherence or boundedness assumption is used, and zero rings and
zero complexes are included.
(blueprint: lem-pc-affine-derived-tensor-chart-comparison). -/
theorem affine_derivedTensor_chart_comparison (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ)
    (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(X, ⊤)) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ⊗
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N)) ≅
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                  (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} Γ(X, ⊤))))))) := by
  sorry

end AlgebraicGeometry
