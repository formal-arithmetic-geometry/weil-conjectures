/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityChernClasses
public import Sheaf.AlgebraicGeometry.CompleteFlagBundle
public import Sheaf.Paper.KummerAdditivity
import Sheaf.Paper.ProjectiveBundleFormula
import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.AlgebraicGeometry.CartierKummerMap
import Sheaf.Paper.ClosedSupportedCupVanishing
import Sheaf.Paper.SupportedCupFunctoriality

/-!
# The Chern polynomial of a bundle filtered by line quotients

Source: Stacks Project, Tags 0FI5 and 0FI7, `proposition-chern-class` and
`lemma-splitting-principle`; blueprint localized-top-Chern Step 4 (L4)
(blueprint: lem-pur-chern-flag-formula).

The polynomial identity is stated coefficient by coefficient in H^(2i)(S,A(i)).
`ordinaryFiniteFlagProductCoefficient` expands the product of the factors 1+x_j u
by the usual coefficient recurrence. Its multiplication is the existing full-support
cup product with the actual Kummer class of the quotient line. Thus no new cohomology
ring or arbitrary multiplication is assumed. `ordinaryFiniteFlagTopProduct` is the
ordered cup product of all the roots, with empty product the coefficient unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary etale Kummer class of the specified invertible module; its exact
comparison inverse image is x=c_(1,A)(M) on the small pro-etale site. The exponent
ell^level works at every positive coefficient level, with no divisibility condition.
Source: Stacks Tags 0FI5, 03PL; lem-pur-kummer-additivity
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagRoot (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (a : S ⟶ Spec (.of P.field.k)) (M : S.Modules) (hM : M.IsInvertible) :
    Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧ :=
  letI := hM
  Etale.kummerFirstChern P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
    S (P.diagonalExponent_isUnit a) (Scheme.Pic.ofIsInvertible M)

/-- The coefficient of u^i in the product of 1+x_j u, in the homogeneous group
H^(2i)(S,A(i)). Append the last factor: b'_0=1 and b'_(i+1)=b_(i+1)+b_i cup x_last.
For zero factors the coefficient sequence is (1,0,0,...). Cup multiplication uses
ordinaryFiniteHyperplaneStep, which applies exact comparison to the given etale root.
Source: Stacks Tag 0FI5, iterated line-subbundle formula
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagProductCoefficient (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    (r : ℕ) → (Fin r →
      (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
        (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) →
      (i : ℕ) → ordinaryFiniteCohomology P S i
  | 0, _, 0 => P.ordinaryFiniteCohomologyOne S
  | 0, _, _ + 1 => 0
  | _ + 1, _, 0 => P.ordinaryFiniteCohomologyOne S
  | r + 1, x, i + 1 =>
      P.ordinaryFiniteFlagProductCoefficient S r (fun j => x j.castSucc) (i + 1) +
        P.ordinaryFiniteHyperplaneStep S (x (Fin.last r)) i
          (P.ordinaryFiniteFlagProductCoefficient S r (fun j => x j.castSucc) i)

/-- The cup product x_0 cup ... cup x_(r-1), beginning with the coefficient unit.
Each new root is multiplied on the right, with the ordered shifted Tate comparison
already used in the ordinary Chern construction. In rank zero this is 1 in H^0(S,A).
Source: Stacks Tag 0FI5, top coefficient of the product of linear factors
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagTopProduct (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    (r : ℕ) → (Fin r →
      (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
        (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) →
      ordinaryFiniteCohomology P S r
  | 0, _ => P.ordinaryFiniteCohomologyOne S
  | r + 1, x => P.ordinaryFiniteHyperplaneStep S (x (Fin.last r)) r
      (P.ordinaryFiniteFlagTopProduct S r (fun j => x j.castSucc))

/-- For every filtration by vector subbundles with invertible successive sheaf
quotients, sum_i c_i(F) u^i = product_j (1+c_(1,A)(Q_j)u), and the top Chern class
is the cup product of all the roots. The first conjunct is exactly the polynomial
identity on its coefficients 0,...,r, in their respective homogeneous groups.
There are no terms above r on either side. The second conjunct states its top
coefficient explicitly. The base may be singular, and the filtration need not split.

Source: Stacks Tags 0FI5 and 0FI7; blueprint localized-top-Chern Step 4 (L4)
(blueprint: lem-pur-chern-flag-formula).

Proof, following the eight steps of the DAG node:
1. The full-support cup product is commutative on even degrees, by
   lem-pur-supported-cup-functoriality. For a positive-rank bundle V, the signed
   relation of def-pur-chern-classes gives the monic polynomial P_V(v). It is unique:
   subtract two relations and use injectivity of the degree-2d, twist-d instance
   of thm-pur-projective-bundle-formula to make every coefficient zero.
2. In rank zero both polynomial expressions and the empty root product are 1.
   In rank one the quotient is F, and lem-pur-projective-bundle-tautological-geometry
   identifies P(F) with S and O(1) with F. The degree-one relation identifies c_1
   with the Kummer class, using lem-pur-kummer-additivity. No P(0) is formed.
3. For r>=2 put L=F_1 and G=F/L. Trivialize the line quotients locally and lift
   their generators successively to get an adapted frame. Deleting the first
   vector gives the rank-(r-1) quotient filtration with the remaining roots.
   Its ambient quotients are locally free, as in def-pur-complete-flag-bundle.
4. In P(F), the subscheme P(G) is where the tautological quotient kills p*L.
   In an adapted frame its local equation is X_0/X_j on j>0 and 1 on j=0.
   This is a nonzerodivisor even over a singular base. The chart formulas in
   lem-pur-projective-bundle-tautological-geometry glue these Cartier equations
   and identify the restricted tautological line with that of P(G).
5. The divisor line is M=O(1) tensor p*L^dual, by def-pc-divisor-line-bundle.
   Kummer additivity and pullback give c_1(M)=h-p*x_1. The projective bundles
   remain separated and finite type, so all the finite-coefficient maps apply.
6. The class a=P_G(h) restricts to zero on P(G) by the defining Chern relation.
   By lem-amb-cartier-kummer-map the Cartier supported class forgets to h-p*x_1;
   lem-pur-supported-hom reads it in supported cohomology. Apply
   lem-pur-closed-supported-cup-vanishing to obtain a(h-p*x_1)=0. Commutativity
   gives (h-p*x_1)P_G(h)=0, verifying the needed divisor-annihilation axiom here.
7. Expand (v-x_1)P_G(v). Its signed coefficients are c_i(G)+x_1 c_(i-1)(G),
   with c_(-1)=0 and c_r(G)=0. Uniqueness from Step 1 identifies these with c_i(F).
   This is the coefficient recurrence for multiplication by 1+x_1 u.
8. Insert the induction formula for G to obtain the product over all roots.
   Extract degree r to obtain ordinaryFiniteFlagTopProduct. All products are
   the recorded full-support cup products in their shifted Tate coordinates.
   Only local adapted frames were used; neither smoothness nor a global splitting
   enters. The empty scheme and all positive coefficient levels are included. -/
theorem chern_flag_formula (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (F : S.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (H : Fin (r + 1) → S.Modules) (ι : ∀ i : Fin (r + 1), H i ⟶ F)
    (d : ∀ j : Fin r, H j.castSucc ⟶ H j.succ)
    (hmono : ∀ i : Fin (r + 1), Mono (ι i))
    (hcompat : ∀ j : Fin r, d j ≫ ι j.succ = ι j.castSucc)
    (hzero : IsZero (H 0)) (hfull : IsIso (ι (Fin.last r)))
    (hsub : ∀ i : Fin (r + 1), (cokernel (ι i)).IsLocallyFree)
    (hQ : ∀ j : Fin r, (cokernel (d j)).IsInvertible) :
    (∀ i : Fin (r + 1), P.ordinaryFiniteChernClass a F r i.val =
      P.ordinaryFiniteFlagProductCoefficient S r
        (fun j => P.ordinaryFiniteFlagRoot a (cokernel (d j)) (hQ j)) i.val) ∧
    P.ordinaryFiniteChernClass a F r r =
      P.ordinaryFiniteFlagTopProduct S r
        (fun j => P.ordinaryFiniteFlagRoot a (cokernel (d j)) (hQ j)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
