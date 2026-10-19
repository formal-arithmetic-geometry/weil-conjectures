/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.TraceFormula.AlgebraicShriekCalculus
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Module.Projective
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.AffineProjectiveComplexDerivedHom
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Mathlib.RingTheory.Noetherian.Basic

/-! # Bounded coherent algebraic upper shriek

Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

## Main statements

* `AlgebraicGeometry.AlgebraicShriekCalculus.shriek_bounded_finite_homology`:
  a perfect polynomial presentation makes upper shriek preserve bounded finite cohomology.
* `AlgebraicGeometry.AlgebraicShriekCalculus.shriek_unit_bounded_finite_homology`:
  the same assertion for the degree-zero regular module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicShriekCalculus

/-- A finite-type map of Noetherian rings, perfect over a polynomial presentation,
sends bounded finite cohomology to bounded finite cohomology under algebraic upper shriek.
The module in the perfectness hypothesis is the regular A-module restricted along p;
it therefore has precisely the prescribed polynomial action.
Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

Proof:
1. The chosen polynomial presentation P = R[x_1,...,x_n] is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. By def-pc-perfect-ring-complex,
   represent A[0] over P by a bounded complex E of finite projective modules in [u,v].
   The polynomial model in lem-trf-algebraic-shriek-calculus computes the restriction
   of upper shriek of K by RHom_P(A, K tensor_R^L P)[n]. No flatness of R to A is used.
2. By lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and
   def-pc-ring-pseudo-coherent-complex, K has a bounded-above finite-free model F.
   Its terms are flat since tensoring with finite free modules is a finite direct sum.
   Lem-pc-module-bounded-flat-kflat makes F K-flat. By lem-pur-derived-change-of-rings,
   L = F tensor_R P computes derived extension and has finite-free P-terms.
3. The monomial basis of def-weil-pbc-mv-polynomial-ring makes P free, hence R-flat:
   tensoring is a direct sum of copies, whose exactness is coordinatewise.
   Lem-weil-pbc-flat-tensor-exact identifies H^j(L) with H^j(F) tensor_R P.
   Thus its cohomology is supported in some interval [a,b].
4. Truncate L below a: use zero below a, coker(d^{a-1}) in degree a, and L^j above a.
   The projection is a quasi-isomorphism by its degreewise cohomology calculation.
   The truncated complex G is bounded in [a,b] and its terms are finite over P,
   including degree a since a quotient of a finite module is finite.
5. Lem-sc-affine-projective-complex-derived-hom represents RHom_P(A,L) by Hom(E,G).
   Its terms are finite sums of Hom_P(E^i,G^{i+t}). By def-weil-pbc-projective-module,
   each E^i is a summand of a finite free module, so these Hom modules are retracts
   of finite sums of G^{i+t}, hence finite. They vanish unless a-v <= t <= b-u.
6. By lem-weil-pbc-noetherian-submodule-finite, kernels of differentials are finite;
   their quotient cohomology modules are finite as well. The polynomial model shifts
   the support interval to [a-v-n,b-u-n]. Exact restriction of scalars identifies
   these P-cohomology modules with the restricted A-cohomology modules. Their finite
   P-generators also generate over A by applying p to coefficients.
7. For the particular case in the companion statement, take K = R[0], whose only
   cohomology is the cyclic module R in degree zero, including when R is the zero ring. -/
theorem shriek_bounded_finite_homology
    (S : AlgebraicGeometry.AlgebraicShriekCalculus.{u})
    {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (_hp : Function.Surjective p)
    (_hc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ)
    (_hperfect : DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of A A))))
    (K : AlgebraicGeometry.algebraicShriekD R)
    (_hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (_hfinite : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    (∃ a b : ℤ, ((S.shriek φ hφ).obj K).IsGE a ∧ ((S.shriek φ hφ).obj K).IsLE b) ∧
      ∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ((S.shriek φ hφ).obj K)) := by
  sorry

/-- In particular, algebraic upper shriek of R[0] has bounded finite A-cohomology.
Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

Proof: Apply the preceding bounded-coherence argument (steps 1--6 of this node)
to K = R[0]. This is step 7 of the node: cohomology vanishes outside degree zero,
and degree-zero cohomology is R, generated by 1. This also covers the zero ring. -/
theorem shriek_unit_bounded_finite_homology
    (S : AlgebraicGeometry.AlgebraicShriekCalculus.{u})
    {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (_hp : Function.Surjective p)
    (_hc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ)
    (_hperfect : DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of A A)))) :
    (∃ a b : ℤ,
      ((S.shriek φ hφ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).IsGE a ∧
      ((S.shriek φ hφ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).IsLE b) ∧
      ∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((S.shriek φ hφ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  sorry

end AlgebraicGeometry.AlgebraicShriekCalculus
