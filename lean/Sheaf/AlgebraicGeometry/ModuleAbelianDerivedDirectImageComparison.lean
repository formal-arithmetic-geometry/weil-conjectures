/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Canonical derived direct image comparison for module coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)
-/

@[expose] public section

-- This shim retains a private API used by an `import all` consumer.
set_option linter.privateModule false

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private alias upstream_evaluation_acyclic := moduleAbelianForget_injective_evaluation_acyclic

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9. -/
private theorem moduleAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  exact upstream_evaluation_acyclic Λ X G W n

end AlgebraicGeometry.Etale
