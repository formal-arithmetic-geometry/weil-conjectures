/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.Topology.ClosedImmersionPushforwardExact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Generic lengths determine the leading Euler-characteristic terms

Source: Stacks Project, Varieties, Tag 0BEN (Lemma 33.45.2)
(blueprint: lem-sc-numerical-polynomial-leading-term).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Generic lengths are positive integers, and subtracting their component contributions
from the twisted Euler characteristic leaves a numerical polynomial of total degree `< d`.
The support is the set of points with nonzero stalk. The equivalence `components` enumerates
exactly its top-dimensional irreducible components. An integral closed immersion with the
specified range gives their reduced induced closed-subscheme structures.

The integer twists and the numerical-polynomial conclusion are written in the form of
`exists_mvPolynomial_eulerChar_tensorPowers` (blueprint: lem-sc-snapper-numerical-polynomial):
`tensorPow` for nonnegative exponents, powers of `dual` for negative ones, a list fold
starting at the module; a rational polynomial agreeing with the function on the whole
integer lattice, which is zero or has total degree `< d` (so it is zero when `d = 0`).

Source: Stacks Project, Varieties, Tag 0BEN
(blueprint: lem-sc-numerical-polynomial-leading-term).

Proof, following the node's five steps:
1. `lem-sc-generic-stalk-finite-length` gives finite generic lengths, positive on the
components and zero elsewhere. `lem-pc-euler-additive` and
`lem-weil-pbc-length-additive-short-exact` make the difference additive.
2. Properness and `lem-weil-pbc-finite-type-over-noetherian` make X Noetherian.
`lem-weil-pbc-coherent-filtration-integral-subschemes` reduces by a coherent filtration to
pushforwards of nonzero coherent ideals on integral closed subschemes V of dimension at most d.
3. For dimension V < d, `lem-sc-snapper-numerical-polynomial` bounds the first term, and every
 d-dimensional generic stalk vanishes, so the component sum is zero.
4. For dimension V = d, use the ideal sequence. Its pushforward is exact by
`lem-sc-closed-immersion-pushforward-exact`; tensoring with invertible modules is exact.
The quotient has smaller-dimensional support. For the structure sheaf of V the generic
length is one, and `lem-pc-projection-formula` with
`lem-sc-cohomology-closed-immersion-pushforward` makes the difference zero. Additivity
`lem-pc-euler-additive` gives the result for the ideal.
5. Sum over the filtration. The nonzero component stalks have positive finite lengths.
For d = 0 there can be no nonzero monomial, so the polynomial is zero. -/
theorem numericalPolynomial_leadingTerm (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (r : ℕ) (L : Fin r → X.Modules) [∀ i : Fin r, (L i).IsInvertible]
    (S : Set X)
    (hS : S = {x : X | ¬ Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x)})
    (d : WithBot ℕ∞) (hd : d = topologicalKrullDim S)
    (s : ℕ)
    (components : Fin s ≃ {C : Set S // C ∈ irreducibleComponents S ∧
      topologicalKrullDim C = d})
    (Z : Fin s → Scheme.{u}) [∀ i, IsIntegral (Z i)]
    (ι : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (ι i)]
    (hι : ∀ i, Set.range (ι i) = Subtype.val '' (components i).val)
    (ξ : Fin s → X) (hξ : ∀ i, IsGenericPoint (ξ i) (Set.range (ι i))) :
    ∃ m : Fin s → ℕ,
      (∀ i, Module.length (X.presheaf.stalk (ξ i)) (F.presheaf.stalk (ξ i)) =
        (m i : ℕ∞) ∧ 0 < m i) ∧
      ∃ P : MvPolynomial (Fin r) ℚ,
        (P = 0 ∨ ((P.totalDegree : ℕ∞) : WithBot ℕ∞) < d) ∧
        ∀ n : Fin r → ℤ, MvPolynomial.eval (fun i => (n i : ℚ)) P =
          (((List.ofFn fun i : Fin r =>
              if 0 ≤ n i then (L i).tensorPow (n i).toNat
              else (L i).dual.tensorPow (-n i).toNat).foldl
                (fun M N : X.Modules => M ⊗ N) F).eulerChar k : ℚ) -
            ∑ i : Fin s, (m i : ℚ) *
              (((List.ofFn fun j : Fin r =>
                  if 0 ≤ n j then (L j).tensorPow (n j).toNat
                  else (L j).dual.tensorPow (-n j).toNat).foldl
                    (fun M N : X.Modules => M ⊗ N)
                    ((pushforward (ι i)).obj (SheafOfModules.unit _))).eulerChar k : ℚ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
