/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Open restriction of injective module resolutions

Restricting an injective resolution of sheaves of modules to an open gives an injective
resolution.

## Implementation details

Restriction is exact and has an exact left adjoint (extension by zero), so it preserves exact
complexes and injective objects.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1), part (1)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Restricting an injective resolution to any open gives an injective resolution,
with the termwise restricted complex and the restricted augmentation. In particular,
every restricted term is injective. The equality `h` identifies the whole complex,
including its differentials; `eqToHom` transports the augmentation's target along `h`. -/
theorem restrict_injectiveResolution (X : RingedSpace.{u}) (U : Opens X)
    (F : SheafOfModules.{u} (moduleRings X)) (I : InjectiveResolution F) :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
    (∃ (J : InjectiveResolution (R.obj F))
      (h : J.cocomplex = (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ eqToHom (congrArg (fun K => K.X 0) h) = R.map (I.ι.f 0)) ∧
    (∀ n : ℕ, Injective (R.obj (I.cocomplex.X n))) := by
  let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
  obtain ⟨hlim, hcolim, hleft, _, ⟨adj⟩⟩ := open_restriction_adjunction_exact X U
  let := hlim
  let := hcolim
  let := hleft
  let : R.PreservesInjectiveObjects :=
    adj.preservesInjectiveObjects_of_preservesFiniteLimits
  have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
    infer_instance
  let e := (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).app F
  let J : InjectiveResolution (R.obj F) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := hinj
      ι := e.inv ≫ (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
      quasiIso := by infer_instance }
  refine ⟨⟨J, rfl, ?_⟩, hinj⟩
  simp [J, e, R]

end AlgebraicGeometry.RingedSpace
