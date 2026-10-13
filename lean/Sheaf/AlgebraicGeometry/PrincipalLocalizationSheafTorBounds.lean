/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Sheaf Tor bounds on principal localizations

Source: Stacks Project, Tags 09U8 and 08DW.
(blueprint: lem-sc-principal-localization-sheaf-tor-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wU wF

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Sheaf Tor bounds on an open containing D(f) hold for the associated-sheaf
complex of the localization, with the same interval. No boundedness, freeness,
or quasi-compactness is required.
Source: Stacks Project, Tag 09U8 (pullback preserves Tor amplitude), and
Tag 08DW(2) (affine derived pullback computation).
(blueprint: lem-sc-principal-localization-sheaf-tor-bounds).

Proof. Identify Spec(A_f) with D(f), and let j:D(f) -> U be its open inclusion.
Given a module sheaf H on D(f), form its ordinary direct image j_*H on U.
Its restriction is H, by the open-immersion adjunction counit. Test the bound
on U against j_*H and restrict its vanishing cohomology to D(f). Restriction
is exact and commutes with derived tensor, so this is precisely the vanishing
for the restricted complex tensored with H. No exactness of j_* is used.
The composite restriction from Spec(A) to D(f) is pullback along the flat
localization map A -> A_f. Termwise localization computes this derived
pullback for any complex, since localization is exact. The affine tilde
pullback comparison identifies its representative with tilde(P_f).
The canonical Shrink equivalence in localizedModuleFunctor gives exactly
P_f, compatibly with differentials. Transport through the scheme isomorphism
Spec(A_f) = D(f) preserves tensors and homology, giving the stated vanishing.
For f=0 both the localized ring and its module sheaves are zero; for a unit
f this is restriction to the whole spectrum. Empty U admits only empty D(f).
The argument uses no relation between a and b, including the empty interval. -/
theorem principal_localization_sheaf_tor_bounds
    (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (U : (Spec (.of A)).Opens)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (a b : ℤ)
    (hamp : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes U.toScheme
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
                (ComplexShape.up ℤ)).obj P))) G i)
    (f : A) (hf : PrimeSpectrum.basicOpen f ≤ U)
    [HasDerivedCategory.{wF}
      (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))] :
    ∀ G : SheafOfModules.{u}
        (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes (Spec (.of (Localization.Away f)))
          (DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
              (SheafOfModules.{u}
                (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace)) _ _ _ _
              (tilde.functor (.of (Localization.Away f))) ⟨fun _ _ ↦ tilde.map_zero⟩
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).mapHomologicalComplex
                (.up ℤ)).obj P))) G i := by sorry

end AlgebraicGeometry
