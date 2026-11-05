/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChange

/-!
# Extension of scalars along a flat ring morphism on derived categories

Let `f : R →+* S` be a flat morphism of commutative rings. Extension of scalars
`S ⊗_R - : ModuleCat R ⥤ ModuleCat S` is exact, so it induces a triangulated functor
`ModuleCat.derivedExtendScalars f hf : D(R) ⥤ D(S)` which commutes with cohomology. It carries
`Dᵇ_fg(R)` into `Dᵇ_fg(S)`, and the multiplication by `r : R` to the multiplication by `f r`.

## Main definitions and statements

- `CategoryTheory.Functor.mapDerivedCategory_map_smul_id`: an exact functor sending the
  multiplication by `r` to the multiplication by `s` does so on derived categories.
- `ModuleCat.derivedExtendScalars`: the functor `D(R) ⥤ D(S)`.
- `ModuleCat.derivedExtendScalars_map_smul_id`: it sends `r • 𝟙` to `f r • 𝟙`.
- `ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj`: it preserves `Dᵇ_fg`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {R S : Type*} [Ring R] [Ring S] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear S C₂]

end CategoryTheory.Functor

namespace ModuleCat

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (f : R →+* S)

open ChangeOfRings

variable (hf : f.Flat)

/-- The extension of scalars `D(R) ⥤ D(S)` along a flat ring morphism `f : R →+* S`, induced by
the exact functor `S ⊗_R -`. -/
noncomputable def derivedExtendScalars :
    DerivedCategory (ModuleCat.{u + 1} R) ⥤ DerivedCategory (ModuleCat.{u + 1} S) :=
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  (extendScalars.{u + 1, u + 1, u + 1} f).mapDerivedCategory

noncomputable instance : (derivedExtendScalars f hf).CommShift ℤ := by
  unfold derivedExtendScalars
  infer_instance

instance : (derivedExtendScalars f hf).IsTriangulated := by
  unfold derivedExtendScalars
  infer_instance

end ModuleCat
