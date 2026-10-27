/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.ImprovePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.RingTheory.SmoothLocalizationConormalSplit
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Conormal stabilization and equations over a smooth open

Source: Elkik, Solutions d'équations à coefficients dans un anneau hensélien,
II, Lemma 3, pp. 562–564, and the equations reduction in Lemma 4, pp. 564–565;
Stacks Project, Tag 07CE, proof of lemma-improve-presentation
(blueprint: lem-per-elkik-conormal-smooth-open-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite presentation admits a retract and one fixed polynomial presentation whose
kernel has equations with unit maximal Jacobian minors on every principal open lying
above the given smooth open.

Source: Elkik II, Lemma 3, pp. 562–564, and Lemma 4, pp. 564–565; Stacks Project,
Tag 07CE, proof of lemma-improve-presentation
(blueprint: lem-per-elkik-conormal-smooth-open-chart).

Proof:
1. Choose B = P₀/I with n variables and m generators of I. Put M = I/I² and
   D = Sym_B(M). Its structure map and augmentation give i and r with ri = 1
   (lem-weil-pbc-symmetric-algebra-universal-property). The m conormal generators
   give a surjection from P = R[x₁,…,xₙ,y₁,…,yₘ]. Set N = n+m and c = m.
   Use lem-weil-pbc-symmetric-algebra-finite-presentation and the finite-type
   Noetherian and Noetherian finite-presentation lemmas to obtain finite presentation.
2. By lem-weil-pbc-improve-presentation, D is smooth over each smooth principal
   localization of B. Principal-localization open immersions and the smooth-ring-map
   versus smooth-affine comparison identify these with an open cover of W.
   Smooth restriction and smoothness local on the source give smoothness above W.
   The split localized conormal sequence makes M finite projective there, hence
   prime-locally finite free by lem-weil-pbc-finite-projective-prime-local-free.
3. For h as in the statement, set T = D[1/p(h)]. Apply
   lem-per-symmetric-conormal-free-locus-exact-sequence over this free locus.
   Its two split sequences identify (J/J²) tensor_D T with T^m. If T = 0, take
   s = 0 and all f_j = 0. Otherwise lift a basis to J, clearing the powers of h
   separately; the resulting f_j still give a basis over T.
4. In P[1/h], this basis gives J = (f_j) + J². Thus E = J/(f_j) satisfies JE = E.
   By lem-weil-pbc-nakayama-one-plus-ideal-annihilator, an element e in 1+J kills E.
   Write e = v/h^b. Then vJ is contained in (f_j) after localization, while p(v)
   is a unit on the prescribed open, so D(p(hv)) = D(p(h)).
5. Since P is Noetherian, finitely many generators of J allow one common denominator
   exponent b. For k at least max(1,b), put s = (hv)^k. Then sJ is contained in (f_j),
   and taking a positive power preserves D(p(s)) = D(p(h)).
6. By smooth localization and lem-weil-pbc-smooth-localization-conormal-split, the
   differential in the conormal basis has a left inverse. Cauchy–Binet expresses 1
   as a combination of its c by c Jacobian minors. The equality of principal opens
   identifies the localizations at p(s) and p(h), giving the required unit ideal.
   For c = 0 the unique empty determinant is 1.
-/
theorem exists_elkik_conormal_smooth_open_chart
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (W : (Spec (CommRingCat.of B)).Opens)
    (hW : Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Algebra.FinitePresentation R D ∧
      ∃ (i : B →ₐ[R] D) (r : D →ₐ[R] B),
        r.comp i = AlgHom.id R B ∧
        ∃ (N c : ℕ), c ≤ N ∧
          ∃ p : MvPolynomial (Fin N) R →ₐ[R] D,
            Function.Surjective p ∧
            ∀ h : MvPolynomial (Fin N) R,
              (∀ q : PrimeSpectrum D, p h ∉ q.asIdeal →
                Spec.map (CommRingCat.ofHom i.toRingHom) q ∈ W) →
              ∃ (s : MvPolynomial (Fin N) R) (f : Fin c → MvPolynomial (Fin N) R),
                (∀ j : Fin c, f j ∈ RingHom.ker p.toRingHom) ∧
                PrimeSpectrum.basicOpen (p s) = PrimeSpectrum.basicOpen (p h) ∧
                (∀ g ∈ RingHom.ker p.toRingHom, s * g ∈ Ideal.span (Set.range f)) ∧
                Ideal.span (Set.range
                  (fun S : {S : Finset (Fin N) // S.card = c} ↦
                    algebraMap D (Localization.Away (p s))
                      (p (Matrix.det (fun j k : Fin c ↦
                        MvPolynomial.pderiv (S.val.orderEmbOfFin S.property k) (f j)))))) = ⊤ := by
  sorry

end AlgebraicGeometry
