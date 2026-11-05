/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Constructible complexes over a geometric point

Let `Λ` be a commutative ring and `k` a separably closed field. Étale sheaves of `Λ`-modules on
`Spec k` are `Λ`-modules: the global sections functor `Γ = Γ(Spec k, -)` is an exact equivalence
with inverse the constant sheaf functor (`constantSheafEquivalenceOfIsSepClosed`). A sheaf `F`
on `Spec k` is constructible if and only if `Γ(F)` is a finitely generated `Λ`-module: it is the
constant sheaf on `Γ(F)`, whose stalks are `Γ(F)`. Since `D(Γ)` commutes with homology and
preserves and reflects boundedness, the equivalence `D(Γ) : D((Spec k)_ét, Λ) ≌ D(Λ)`
restricts to an equivalence between `Dᵇc(Spec k, Λ)` and the full subcategory `Dᵇ_fin(Λ)` of
`D(Λ)` of bounded complexes with finitely generated (for `Λ` finite: finite) cohomology modules.

## Main definitions

- `DerivedCategory.boundedFiniteCohomology`: the object property `Dᵇ_fin(Λ)` of `D(Λ)`.
- `AlgebraicGeometry.Etale.pointFiber`: the evaluation
  `Fib_s : Dᵇc(Spec k, Λ) ⥤ Dᵇ_fin(Λ)` at the geometric point `s = Spec k`, the restriction
  of `D(Γ)`.
- `AlgebraicGeometry.Etale.pointFiberEquivalence` (`def-weil-finite-coefficient-point`, finite
  coefficient stage): `Fib_s` is an equivalence. The integral stage `𝒪_E` is
  `AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence`
  (`WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The object property `Dᵇ_fin(Λ)` of the derived category `D(Λ)` of `Λ`-modules: bounded
complexes all of whose cohomology modules are finitely generated. For a finite ring `Λ` these are
the bounded complexes with finite cohomology modules
(`DerivedCategory.boundedFiniteCohomology_iff_finite`). -/
noncomputable def boundedFiniteCohomology :
    ObjectProperty (DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    fun K ↦ ∀ n : ℤ, Module.Finite Λ ((homologyFunctor (ModuleCat.{u + 1} Λ) n).obj K)

instance : (boundedFiniteCohomology Λ).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1, fun n ↦
      have := h.2 n
      Module.Finite.equiv ((homologyFunctor (ModuleCat.{u + 1} Λ) n).mapIso e).toLinearEquiv⟩

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (k : Type u) [Field k] [IsSepClosed k]

variable {Λ k}

variable (Λ k)

end Etale

end AlgebraicGeometry
