/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.Algebra.Category.ModuleCat.TorSymmetry
import Sheaf.Algebra.TorDimensionShifting
import Sheaf.AlgebraicGeometry.ProjectiveSpace.KoszulResolution

/-!
# Vanishing of first Tor for second syzygies over two variables

Source: blueprint `lem-sc-p1-graded-resolution`, Koszul resolution and dimension shifting.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace MvPolynomial

/-- The second kernel of two finite free surjections has vanishing first Tor with `k`.
Source: blueprint `lem-sc-p1-graded-resolution`, proof, Koszul resolution and dimension shifting
(blueprint: lem-sc-p1-second-syzygy-tor-vanishes).

Proof: the two surjections give short exact sequences
`0 → ker q₀ → F₀ → M → 0` and `0 → ker q₁ → F₁ → ker q₀ → 0`.
If the universe of `M` differs from the ring universe, replace it by the small quotient
`F₀ / ker q₀` using the first isomorphism theorem; this leaves both kernels unchanged.
The displayed finite bases make both middle terms free. Apply the first, natural-isomorphism
clause of `tor_dimension_shifting` to identify `Tor₁(ker q₁,k)` with `Tor₃(M,k)`.
Use `nonempty_tor'_flip_iso` to identify the latter with `Tor₃(k,M)`. The explicit exact
Koszul complex `koszul_resolution` resolves `S/(X 0,X 1)` by the free modules `S`, `S²`, `S`.
Its last quotient is canonically the restriction of scalars of `k` along `constantCoeff`:
the kernel of constant coefficient is precisely `(X 0,X 1)`, as every nonconstant monomial
is divisible by a variable. Package this complex as a projective resolution and compute Tor
by tensoring it with `M`. The complex is zero in degree three, so its third homology is zero.
Transport this zero object across symmetry and dimension shifting and use the equivalence
between zero module objects and subsingleton carriers. No grading assumption is needed for
this vanishing. The argument also applies when either free module has rank zero. -/
theorem second_syzygy_tor_vanishes {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (F₀ F₁ : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (r₀ r₁ : ℕ)
    (b₀ : Module.Basis (Fin r₀) (MvPolynomial (Fin 2) k) F₀)
    (b₁ : Module.Basis (Fin r₁) (MvPolynomial (Fin 2) k) F₁)
    (q₀ : F₀ →ₗ[MvPolynomial (Fin 2) k] M) (hq₀ : Function.Surjective q₀)
    (q₁ : F₁ →ₗ[MvPolynomial (Fin 2) k] q₀.ker) (hq₁ : Function.Surjective q₁) :
    Subsingleton (((Tor' (ModuleCat.{u} (MvPolynomial (Fin 2) k)) 1).obj
      (ModuleCat.of (MvPolynomial (Fin 2) k) q₁.ker)).obj
      ((ModuleCat.restrictScalars
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k)).obj
        (ModuleCat.of k k))) := by sorry

end MvPolynomial
