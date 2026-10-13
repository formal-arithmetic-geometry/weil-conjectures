/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Exactness of the ideal homology connecting map

Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
(blueprint: lem-weil-pbc-tor-ideal-homology-exactness)

Proof in words: every quotient tensor is represented by y ⊗ 1, since a scalar
in R/I lifts to R; every differential of a quotient cycle belongs to I P₀,
so it has a finite expression Σ a_j p_j. The formula implies μ δH = 0
because ε d = 0. Conversely a tensor in ker μ lifts through I ⊗ P₀ by
right exactness. Its image in P₀ is killed by ε, hence is d y by resolution
exactness, giving a quotient cycle whose image is the original tensor.
For injectivity, if δH of a quotient cycle is zero, right exactness for
I ⊗ P identifies its ideal-tensor lift as an ideal-tensor boundary. Subtract
the corresponding element of I P₁ from y; the difference is an actual cycle
in P₁. Exactness of P in degree one makes it a boundary from P₂. Reducing
modulo I shows the original quotient cycle is a boundary. Thus δH is injective.
These arguments include the zero ideal, unit ideal and zero module.
-/
theorem tor_ideal_homology_exactness
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (μR : (I ⊗[R] M) →ₗ[R] M)
    (hμR : ∀ (a : I) (x : M), μR (a ⊗ₜ[R] x) = (a : R) • x)
    (δH : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 1 →ₗ[R] (I ⊗[R] M))
    (hδH : ∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δH
          (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) :
    Function.Injective δH ∧ LinearMap.range δH = LinearMap.ker μR := by sorry

end ModuleCat
