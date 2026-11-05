/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-!
# Exact monoidal functors preserve internal homs out of finitely presented modules

Let `R` be a commutative ring and let `F : ModuleCat R ⥤ D` be a lax monoidal functor to a
braided monoidal closed preadditive category, with invertible unit map, which is additive, left
exact and preserves epimorphisms; for instance the constant sheaf functor on a site. Then for
every finitely presented module `P` the comparison map `F [P, Q] ⟶ [F P, F Q]` is an
isomorphism (`ModuleCat.isIso_ihomComparison_app_of_finitePresentation`): it is one for
`P = R`, hence for the finite free modules, and a finitely presented module is the cokernel of a
morphism of finite free modules.
-/

@[expose] public section

universe u

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

variable {R : Type u} [CommRing R] {D : Type*} [Category* D] [Preadditive D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  (F : ModuleCat.{u} R ⥤ D) [F.LaxMonoidal] [IsIso (ε F)] [F.Additive]
  [PreservesFiniteLimits F] [F.PreservesEpimorphisms]

end ModuleCat

namespace Module.Finite

/-- Over a noetherian ring, the module of linear maps between finitely generated modules is
finitely generated: it embeds into `(Rⁿ →ₗ N) ≅ Nⁿ` along a surjection `Rⁿ ⟶ M`. -/
theorem linearMap_of_isNoetherianRing {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] : Module.Finite R (M →ₗ[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact Module.Finite.of_injective (LinearMap.lcomp R N f) fun a b h ↦
    (LinearMap.cancel_right hf).1 h

end Module.Finite
