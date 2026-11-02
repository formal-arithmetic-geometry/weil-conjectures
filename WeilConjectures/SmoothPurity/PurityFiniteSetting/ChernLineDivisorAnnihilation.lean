/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernLineDivisorAnnihilationPositive
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernLineDivisorRankZero

/-! # The relative hyperplane divisor annihilates the lower Chern polynomial

Source: Stacks Project, Tag 0FI5, proposition-chern-class, invertible-submodule paragraph.
(blueprint: lem-pur-chern-line-divisor-annihilation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The geometric vanishing equation before any candidate coefficient is considered.
The lower polynomial is evaluated on P(F), not on P(G).

Source: Stacks Project, Tag 0FI5, proposition-chern-class, restriction-zero argument;
Cohomology Tags 0G75, 0G76, 0G77 for the supported cup action.
(blueprint: lem-pur-chern-line-divisor-annihilation).

Proof: if n=0, use the proved rank-zero-quotient case: the two line quotient
isomorphisms identify the roots, so multiplication by their difference is zero.
If n is positive, use the Cartier divisor restriction-zero argument, which is
stated independently of the candidate coefficients and of this rank edge case. -/
theorem lineSubbundleChernPolynomial_annihilation (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank (n + 1)] [G.IsFiniteLocallyFreeOfRank n]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (D : ProjectiveBundleRealization S F) (hD : D.L.IsInvertible)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.ordinaryFiniteHyperplaneStep D.A.data.relProj
      (P.ordinaryFiniteLineDivisorRoot a L D hD) n
      (P.ordinaryFiniteProjectivePolynomialValue t a D hD n
        (P.ordinaryFiniteChernClasses a G n)) = 0 := by
  cases n with
  | zero =>
    exact lineSubbundleChernPolynomial_annihilation_rankZero P a L F G ι π w hexact D hD t
  | succ n =>
    exact lineSubbundleChernPolynomial_annihilation_positive P a (n + 1) (by omega)
      L F G ι π w hexact D hD t

end WeilConjectures.PurityFiniteSetting
