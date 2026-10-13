/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # Transport of perfect models from an open subscheme

Source: Stacks Project, Definition 08CM, Definition 08C4 and restriction in Tag 08DW.
(blueprint: lem-sc-open-perfect-model-transport).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect model on an open subscheme is an ambient local perfect model.
Source: Stacks Project, Definition 08CM, Definition 08C4 and Tag 08DW.
(blueprint: lem-sc-open-perfect-model-transport).

Proof: Fix x in U and choose an open V of U and a strictly perfect complex K
representing F near x, using IsPerfect. Set O = U.ι image V. This is open in X
and contains x. The isomorphism U.ι.isoImage V identifies V.toScheme with
O.toScheme. Compose Modules.overEquiv V, restriction along the inverse of that isomorphism,
and the inverse of Modules.overEquiv O to obtain an exact additive equivalence
A of their localized module categories. Its unit-module comparison, together
with preservation of coproducts, identifies A of each finite free module with
the corresponding finite free module. Apply A degreewise to K. The same degree
bounds hold because A preserves zero objects. If i and p split a term off a
finite free module, their images, composed with the finite free comparison,
still satisfy i followed by p = identity. Thus the transported complex is
strictly perfect. The restriction-composition comparison for V.ι followed by
U.ι, and U.ι.isoImage V, identifies its representing derived object with
R restricted to O: apply restriction to e and compose with the given model
isomorphism, the derived equivalence comparisons and A.mapDerivedCategoryFactors.
This gives the required K and model isomorphism. Empty U has no points; zero F
and the total open use the same construction. No condition is imposed outside U. -/
theorem local_perfect_of_openRestriction_iso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (R : schemeDerivedCategory X)
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (e : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ F) :
    ∀ x : X, x ∈ U → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K) := by sorry

end AlgebraicGeometry.Scheme
