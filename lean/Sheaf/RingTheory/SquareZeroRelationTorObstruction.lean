module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Eval
import Sheaf.RingTheory.DividedPowerDGA

/-! # A lifted relation obstructing finite Tor dimension

Source: Stacks Project, `dpa.tex`, Tag 09PU, `lemma-not-finite-pd`.
(blueprint: lem-sfb-square-zero-relation-tor-obstruction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A relation lifted to a nonnilpotent multiple of the generator of a cyclic square-zero
kernel obstructs finite Tor dimension. Here `I` is the image of the annihilator of `(f)`
in the source ring: since the kernel is square-zero, this is exactly the annihilator of
`f` for the action of the quotient ring by lifts. `J` names the ideal of relations, and
`Ideal.map ((Ideal.Quotient.mk J).comp MvPolynomial.C) I` is the ideal `IS` in `S`.

Source: Stacks Project, `dpa.tex`, Tag 09PU, `lemma-not-finite-pd`.
(blueprint: lem-sfb-square-zero-relation-tor-obstruction).

Proof: Apply lem-sfb-tate-free-resolution to the quotient of the polynomial ring by J.
The resulting divided-power DGA A is a free R-resolution of S, with H_0(A) = S and
vanishing positive homology. Apply lem-sfb-square-zero-dga-curvature to obtain the
lifted differential and its degree-minus-two curvature theta on B = A/IA. The relation,
its chosen lifts and H_1(A) = 0 satisfy lem-sfb-lifted-relation-curvature-class, giving
a cycle z in B_2 with [theta(z)] equal to the image of g' in S/IS.
Put t = theta(z). The differential identity of def-sfb-divided-power-dga makes every
gamma_a(z) a cycle. The curvature identities imply theta(t) = 0 and inductively
theta^k(gamma_a(z)) = t^k gamma_(a-k)(z) for 0 <= k <= a. Thus
theta^a(gamma_a(z)) = t^a. If gamma_a(z) were a boundary, commutation with the
differential would make t^a a boundary, contradicting the nonnilpotence hypothesis.
Consequently H_(2a)(B) is nonzero for every positive a. Tensoring the free resolution
A with R/I gives B, by the mutually inverse maps a tensor r-bar to ra mod IA and
a-bar to a tensor 1. By def-weil-pbc-tor-modules, this identifies H_i(B) with
Tor'_i(S,R/I). A uniform bound d would kill the nonzero group in degree 2(d+1),
a contradiction. -/
theorem square_zero_relation_not_finite_tor_dimension
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing R']
    (q : R' →+* R) (hq : Function.Surjective q) (f : R')
    (hker : RingHom.ker q = Ideal.span {f})
    (hsq : (Ideal.span {f} : Ideal R') ^ 2 = ⊥)
    (I : Ideal R) (hI : I = Ideal.map q (Ideal.span {f}).annihilator)
    (n m : ℕ) (h r : Fin m → MvPolynomial (Fin n) R)
    (hrel : ∑ j, r j * h j = 0)
    (hcoeff : ∀ (j : Fin m) (d : Fin n →₀ ℕ), (r j).coeff d ∈ I)
    (J : Ideal (MvPolynomial (Fin n) R)) (hJ : J = Ideal.span (Set.range h))
    (h' r' : Fin m → MvPolynomial (Fin n) R') (g' : MvPolynomial (Fin n) R')
    (hlift : ∀ j : Fin m, MvPolynomial.map q (h' j) = h j)
    (rlift : ∀ j : Fin m, MvPolynomial.map q (r' j) = r j)
    (hrel' : ∑ j, r' j * h' j = g' * MvPolynomial.C f)
    (hg : ¬ IsNilpotent
      (Ideal.Quotient.mk (Ideal.map ((Ideal.Quotient.mk J).comp MvPolynomial.C) I)
        (Ideal.Quotient.mk J (MvPolynomial.map q g')))) :
    ¬ ∃ d : ℕ, ∀ (N : ModuleCat.{u} R) (i : ℕ), d < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj
        (ModuleCat.of R (MvPolynomial (Fin n) R ⧸ J))).obj N) := by
  sorry

end ModuleCat
