/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.AlgebraicGeometry.Properties

/-!
# Nonzero sections on integral schemes

Source: `literature/stacks-project/divisors.tex`, Lemma 02OR (blueprint:
`lem-pc-nonzero-section-integral-cartier`).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- A nonzero section of an invertible module on an integral scheme has an effective
Cartier zero scheme, with the expected local equation on each affine trivialization.

Source: Stacks Project, Divisors, Lemma 02OR
(blueprint: lem-pc-nonzero-section-integral-cartier).

Proof: let `U = Spec A` be a nonempty affine open on which `M` is free on `e`, and write
`s|_U = a • e`. Since `X` is integral and `M` is invertible, restriction `Γ(M, ⊤) → Γ(M, U)`
is injective (`lem-sc-invertible-module-generic-stalk`, clause 3), so `s|_U ≠ 0` and hence
`a ≠ 0`. As `X` is integral, `A` is a domain, so `a` is a nonzerodivisor; by the local form of
the zero scheme (`lem-pc-zero-scheme-properties`, clause 1) the ideal of `Z(s)` on `U` is `(a)`.
Such `U` cover `X` since `M` is invertible, so the ideal of `Z(s)` is an effective Cartier
ideal.
-/
theorem nonzero_section_integral_cartier [IsIntegral X] (M : X.Modules)
    [M.IsInvertible] (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    (∀ (U : X.affineOpens) (_ : Nonempty U.1) (e : Γ(M, U.1))
      (he : IsFreeGenerator e),
        IsFreeGenerator.coeff (M := M) (U := U.1) (e := e) he
            (M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) ≠ 0 ∧
          (homOfGlobalSection M s).zeroLocus.ideal U =
            Ideal.span {IsFreeGenerator.coeff (M := M) (U := U.1) (e := e) he
              (M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)} ∧
          IsFreeGenerator.coeff (M := M) (U := U.1) (e := e) he
              (M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) ∈
            nonZeroDivisors Γ(X, U.1)) ∧
      (homOfGlobalSection M s).zeroLocus.IsInvertible := by sorry

end Modules
end Scheme
end AlgebraicGeometry
