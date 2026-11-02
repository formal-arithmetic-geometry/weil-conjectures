/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernFlagFormula
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClasses

/-! # Evaluating the monic signed Chern polynomial

Source: Stacks Project, Tag 0FI5, equation-chern-classes.
(blueprint: def-pur-chern-projective-polynomial-value).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The actual evaluation of the monic signed polynomial, as leading power minus
its signed lower-coefficient sum. No relation or vanishing is built into the data.
Source: Stacks Project, Tag 0FI5 (blueprint: def-pur-chern-projective-polynomial-value). -/
def ordinaryFiniteProjectivePolynomialValue (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {S : Scheme.{u}} {F : S.Modules}
    (a : S ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization S F)
    (hD : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : ℕ, P.ordinaryFiniteCohomology S i) :
    P.ordinaryFiniteCohomology D.A.data.relProj r :=
  (P.ordinaryFiniteHyperplaneProduct D.A.data.relProj (P.projectiveBundleChern a D hD)
    0 (P.ordinaryFiniteCohomologyOne D.A.data.relProj) r ≫
      eqToHom (congrArg (P.diagonalTwist D.A.data.relProj) (Nat.zero_add r))) -
    ∑ i : Fin r, (-1 : ℤ) ^ i.val •
      (P.ordinaryFiniteHyperplaneProduct D.A.data.relProj (P.projectiveBundleChern a D hD)
        (i.val + 1)
        (P.ordinaryFiniteCohomologyPullback t D.A.data.relProjHom
          (P.diagonalExponent_isUnit a) (i.val + 1) (c (i.val + 1)))
        (r - (i.val + 1)) ≫
        eqToHom (congrArg (P.diagonalTwist D.A.data.relProj)
          (Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt))))

/-- The root of the relative Cartier hyperplane line, written h minus the pulled
first-line root, using the actual tensor pullback of L.
Source: Stacks Project, Tag 0FI5 (blueprint: def-pur-chern-projective-polynomial-value). -/
def ordinaryFiniteLineDivisorRoot (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} {F : S.Modules} (a : S ⟶ Spec (.of P.field.k))
    (L : S.Modules) [L.IsInvertible] (D : ProjectiveBundleRealization S F)
    (hD : D.L.IsInvertible) :=
  let hL : ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso D.A.data.relProjHom).app L).symm
  P.projectiveBundleChern a D hD -
    P.ordinaryFiniteFlagRoot (D.A.data.relProjHom ≫ a)
      ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj L) hL

/-- The concrete candidate coefficients for multiplication by the first line factor.
Source: Stacks Project, Tag 0FI5, expansion of (v-x)P_G(v).
(blueprint: def-pur-chern-projective-polynomial-value). -/
def lineSubbundleChernCandidate (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (L G : S.Modules) (hL : L.IsInvertible) [G.IsFiniteLocallyFreeOfRank n] :
    ∀ i : ℕ, P.ordinaryFiniteCohomology S i
  | 0 => P.ordinaryFiniteCohomologyOne S
  | i + 1 => P.ordinaryFiniteChernClass a G n (i + 1) +
      P.ordinaryFiniteHyperplaneStep S (P.ordinaryFiniteFlagRoot a L hL) i
        (P.ordinaryFiniteChernClass a G n i)

end WeilConjectures.PurityFiniteSetting
