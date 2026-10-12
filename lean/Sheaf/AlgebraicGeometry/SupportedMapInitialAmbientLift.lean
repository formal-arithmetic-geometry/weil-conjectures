/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.Algebra.Homology.OpenExtensionRestrictionIso
import Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps

/-! # Initial ambient representative of a supported perfect map

Source: Stacks Project, Tags 08BT and 09IM.
(blueprint: lem-sc-supported-map-initial-ambient-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A supported perfect source and map on an open have an ambient representative
which is perfect and supported at the points of that open. No perfectness is asserted
outside the open.
Source: Stacks Project, Tags 08BT, 00A7 (4), and 09IM (initial object of the induction).
(blueprint: lem-sc-supported-map-initial-ambient-lift).

Proof: Apply the inverse of Modules.overEquiv U to F and then exact extension by
zero to X. These are actual functors: no arbitrary existence witness defines the
source. The exact extension-by-zero/restriction adjunction induces a derived
adjunction. The adjoint of α, after the equivalence comparisons, is β. The unit
is invertible since extension by zero restricts to the identity on U. Let e be
its inverse, transported to the open subscheme. The adjunction unit equation gives
β restricted to U = e.hom followed by α. At x in U extension by zero has the same
cohomology stalk as F, proving support. Transport a strictly perfect local model
of F at x along the equivalence of the localized site with the open subscheme.
The bounded complex and its finite-free retracts transport termwise, providing
O and K in the displayed local perfectness condition. The construction works for
empty U and zero F, and does not assert that extension by zero is globally perfect. -/
theorem exists_supported_map_initial_ambient_lift
    (X : Scheme.{u}) (U : X.Opens) (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (hFT : ∀ (i : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))
    (α : F ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E.obj) :
    ∃ (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      (∀ x : X, x ∈ U → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)) ∧
      (∀ (i : ℤ) (x : X), x ∈ U → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ F,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = e.hom ≫ α := by sorry

end AlgebraicGeometry.Scheme
