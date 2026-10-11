/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Open restriction of injective module resolutions

Source: Stacks Project, Cohomology, Lemma 01E1, part (1) and proof
(blueprint: lem-sc-ringed-space-restrict-injective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Restricting an injective resolution to any open gives an injective resolution,
with the termwise restricted complex and the restricted augmentation. In particular,
every restricted term is injective. The equality `h` identifies the whole complex,
including its differentials; `eqToHom` transports the augmentation's target along `h`.

Source: Stacks Project, Cohomology, Lemma 01E1, part (1) and proof
(blueprint: lem-sc-ringed-space-restrict-injective-resolution).

Proof: By `lem-sc-derived-open-restriction-adjunction-exact`, restriction is exact,
so it preserves the augmented exact complex of `def-sp-injective-resolutions`.
The same lemma gives an exact left adjoint, extension by zero. Apply
`lem-sp-right-adjoint-preserves-injectives` to obtain injectivity of every restricted
term. By `lem-sc-ringed-space-module-sheaves-enough-injectives`, the module category
on the open is abelian and has enough injectives. Exactness and injectivity give the
claimed resolution, using `def-sp-injective-resolutions`; its degree-zero augmentation
is the restriction of the original one. -/
theorem restrict_injectiveResolution (X : RingedSpace.{u}) (U : Opens X)
    (F : SheafOfModules.{u} (moduleRings X)) (I : InjectiveResolution F) :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
    (∃ (J : InjectiveResolution (R.obj F))
      (h : J.cocomplex = (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ eqToHom (congrArg (fun K => K.X 0) h) = R.map (I.ι.f 0)) ∧
    (∀ n : ℕ, Injective (R.obj (I.cocomplex.X n))) := by
  sorry

end AlgebraicGeometry.RingedSpace
