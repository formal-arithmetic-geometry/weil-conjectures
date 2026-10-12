/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.HilbertDifference
import Sheaf.AlgebraicGeometry.RegularMeromorphicSectionExists
import Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints
import Sheaf.Paper.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Snapper's numerical polynomial for several invertible twists

Source: Stacks Project, Varieties, Lemma 33.45.1, Tag 0BEM, in Section 0BEL
(blueprint: lem-sc-snapper-numerical-polynomial).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The Euler characteristic of a coherent module twisted by integer powers of finitely
many invertible modules is a rational polynomial, integer-valued on the integer lattice,
of total degree at most the dimension of the coherent module's support.
Source: Stacks Project, Varieties, Lemma 33.45.1, Tag 0BEM
(blueprint: lem-sc-snapper-numerical-polynomial).

Integer powers use `tensorPow` for nonnegative exponents and powers of `dual` for negative
exponents. The list fold starts at `F` and tensors the factors in their given order.
The support is the subspace of points with nonzero stalk. The zero polynomial has degree
minus infinity, expressed separately because `MvPolynomial.totalDegree 0 = 0`.

Proof (for stage 3):
1. Induct on the support dimension. In dimension zero, invertible twists preserve Euler
   characteristic by `lem-pc-chi-zero-dim-support`, giving a constant polynomial. The zero
   sheaf, including the case of an empty scheme, gives the zero polynomial.
2. Remove embedded associated points using `lem-sc-hilbert-embedded-points`. Its kernel has
   smaller support dimension, so `lem-pc-euler-additive` reduces to the quotient. Use
   `lem-weil-pbc-scheme-theoretic-support` and
   `lem-weil-pbc-closed-immersion-coherent-equivalence` to write the quotient as a direct
   image from its scheme-theoretic support; `lem-pc-closed-immersion-coherent-cohomology`
   preserves the twisted Euler characteristics. Faithfulness embeds the structure sheaf
   locally into a finite sum of copies of the module, so its associated points are among
   those of the module. Thus the support scheme has no embedded points.
3. For each coordinate, `lem-sc-regular-meromorphic-section-exists` supplies a regular
   meromorphic section. Apply `lem-sc-hilbert-difference` to the quotient twisted by the
   other factors. Its forward difference is a difference of Euler characteristics of
   coherent modules of strictly smaller support dimension.
4. Induction makes every first difference a numerical polynomial of degree at most d-1.
   The arithmetic argument of Tag 0BEM integrates coordinate differences, fixing the
   constant on the zero slice, and repeats on the remaining slice. It produces a rational
   polynomial of total degree at most d on the entire integer lattice.
5. Add the smaller-degree kernel contribution by `lem-pc-euler-additive` to obtain the
   asserted bound for the original module. -/
theorem exists_mvPolynomial_eulerChar_tensorPowers
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (r : ℕ) (L : Fin r → X.Modules) [∀ i : Fin r, (L i).IsInvertible] :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ ((P.totalDegree : ℕ∞) : WithBot ℕ∞) ≤
        topologicalKrullDim
          {x : X | ¬ Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x)}) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun i => (n i : ℚ)) P =
        (((List.ofFn fun i : Fin r =>
          if 0 ≤ n i then (L i).tensorPow (n i).toNat
          else (L i).dual.tensorPow (-n i).toNat).foldl
            (fun M N : X.Modules => M ⊗ N) F).eulerChar k : ℚ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
