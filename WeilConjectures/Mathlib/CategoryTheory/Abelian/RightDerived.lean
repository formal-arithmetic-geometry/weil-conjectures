/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!

# Acyclic resolutions compute right derived functors

Let `v : C ⥤ D` be an additive left exact functor between abelian categories, with `C`
having enough injectives, and let `X : C`. A resolution `X ⟶ I⁰ ⟶ I¹ ⟶ ⋯` of `X` by
objects which are *`v`-acyclic*, i.e. whose higher right derived functors
`Rᵠv` vanish, computes the right derived functors of `v`:

`Hᵠ(v(I⁻))  ≅  Rᵠv X`.

This is the standard replacement of an injective resolution by a cheaper one; it is the
step of the proof of the proper base change theorem which identifies the complex
`f'_* g'⁻¹ I⁻` with `Rf'_* g'⁻¹ E` once every `g'⁻¹ Iᵐ` is known to be `f'_*`-acyclic.

Only the statement is recorded here. The proof breaks the resolution into the short exact
sequences `0 ⟶ Zᵐ ⟶ Iᵐ ⟶ Zᵐ⁺¹ ⟶ 0` and shifts dimensions along their long exact
sequences; no spectral sequence is involved.

## Main statements

- `CategoryTheory.Functor.nonempty_homologyIso_rightDerived_of_acyclic`: the cohomology of
  a termwise `v`-acyclic resolution computes the right derived functors of `v`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Blueprint `sk-thm-acyclicity`: Acyclicity criterion.

Let `v : C ⥤ D` be a left exact additive functor between abelian categories, `C` having
enough injectives. If `π : X ⟶ I⁻` is a resolution of `X : C` by a cochain complex whose
terms are `v`-acyclic — that is, `Rᵠv Iᵐ = 0` for all `q > 0` — then the cohomology of
the complex `v(I⁻)` computes the right derived functors of `v` at `X`:

`Hᵠ(v(I⁻)) ≅ Rᵠv X`.

An injective resolution is the special case in which every `Iᵐ` is injective. -/
theorem nonempty_homologyIso_rightDerived_of_acyclic (v : C ⥤ D) [v.Additive]
    [PreservesFiniteLimits v] {X : C} {I : CochainComplex C ℕ}
    (π : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso π]
    (hI : ∀ m q : ℕ, 0 < q → IsZero ((v.rightDerived q).obj (I.X m))) (q : ℕ) :
    Nonempty (((v.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology q ≅
      (v.rightDerived q).obj X) :=
  sorry

end CategoryTheory.Functor
