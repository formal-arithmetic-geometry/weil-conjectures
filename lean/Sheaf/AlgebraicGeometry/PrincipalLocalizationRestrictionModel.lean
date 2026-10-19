/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! # Principal localization restriction model

Source: Stacks Project, Tag 08DW.
(blueprint: lem-sc-principal-localization-restriction-model).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wX wU wF

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The localized associated-sheaf complex is restriction through an open immersion
into any open containing D(f). Source: Stacks Project, Tag 08DW(2).
(blueprint: lem-sc-principal-localization-restriction-model).
Proof. The localization spectrum map identifies Spec(A_f) with the open D(f).
Factor its open immersion through U using D(f) ≤ U. Compose exact restriction from
Spec(A) to U with restriction along this factorization. The composition comparison
identifies the result with restriction along the localization spectrum map. The
termwise tilde pullback comparison identifies this with tilde of extension of scalars.
The concrete tensor pullback and ordinary restriction are both left adjoint to
module pushforward, so uniqueness of left adjoints supplies their natural comparison.
For localization, extension of scalars is naturally isomorphic to localizedModuleFunctor:
use the universal property of module localization and its canonical Shrink equivalences.
These natural isomorphisms induce complex isomorphisms, respecting differentials.
Localization and restriction are exact, so their factorization comparisons through Q
identify the displayed derived objects for arbitrary complexes. No resolution or
boundedness is necessary. For f=0 the spectrum is empty and the constructions still
apply; for a unit the localization spectrum map is an isomorphism. -/
theorem principalLocalization_restriction_model
    (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (U : (Spec (.of A)).Opens)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (f : A) (hf : PrimeSpectrum.basicOpen f ≤ U)
    [HasDerivedCategory.{wF}
      (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))] :
    ∃ j : Spec (.of (Localization.Away f)) ⟶ U.toScheme,
      ∃ hj : IsOpenImmersion j,
        letI := hj
        ∃ R : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
            SheafOfModules.{u}
              (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace),
          Nonempty (R ≅ Scheme.Modules.restrictFunctor j) ∧
          ∃ hAdd : R.Additive, ∃ hLim : PreservesFiniteLimits R,
            ∃ hCol : PreservesFiniteColimits R,
              letI := hAdd
              letI := hLim
              letI := hCol
              Nonempty ((R.mapDerivedCategory.obj
          ((@Functor.mapDerivedCategory
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _
            ((SheafOfModules.overFunctor.{u}
                (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
              Equivalence.functor
                (C := SheafOfModules.{u}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
                (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
                (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
                (ComplexShape.up ℤ)).obj P)))) ≅
          (DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
              (SheafOfModules.{u}
                (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace)) _ _ _ _
              (tilde.functor (.of (Localization.Away f))) ⟨fun _ _ ↦ tilde.map_zero⟩
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).mapHomologicalComplex
                (.up ℤ)).obj P)))) := by sorry

end AlgebraicGeometry
