/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.LocalRing

/-!
# Testing Tor amplitude at the residue field

Let `R` be an Artinian local ring with residue field `κ`, for instance the finite coefficient
ring `A_{E,n} = 𝒪_E/ϖⁿ`. An object `C` of `D(R)` has Tor amplitude in `[a, b]` as soon as
`C ⊗ᴸ κ` has cohomology in `[a, b]`; the converse is the definition of Tor amplitude. This is the
module-theoretic half of blueprint `lem-exc-residue-tor-test`.

## Proof

Represent `C` by a K-flat complex `P` of flat modules, so that `C ⊗ᴸ M[0]` is the complex
`P ⊗ M`. For a fixed degree `q`, the class of modules `M` for which `P ⊗ M` is exact at `q` is
closed under extensions (`LinearMap.exact_rTensor_of_exact`, a diagram chase using the flatness
of `P^{q+1}`) and under directed unions of finitely generated submodules
(`LinearMap.exact_rTensor_of_forall_finite`). Every finitely generated module over the Artinian
local ring `R` is an iterated extension of copies of `κ`, by induction on its length, so the
class contains every module as soon as it contains `κ`.

No boundedness or finiteness of `C` is needed.

## Main statements

- `LinearMap.exact_rTensor_of_exact_rTensor_residueField`: the module-theoretic core.
- `DerivedCategory.torAmplitudeIn_of_homologyConcentratedIn_tensor_residueField` and
  `DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory TensorProduct Function

namespace LinearMap

variable {R : Type u} [CommRing R] {P₀ P₁ P₂ : Type*} [AddCommGroup P₀] [Module R P₀]
  [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (f : P₀ →ₗ[R] P₁) (g : P₁ →ₗ[R] P₂)

variable [IsLocalRing R] [IsArtinianRing R]

end LinearMap

namespace DerivedCategory

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

end General

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

end DerivedCategory
