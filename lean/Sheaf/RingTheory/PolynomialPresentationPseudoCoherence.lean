module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent

/-!
# Pseudo-coherence and finite polynomial presentations

Source: Stacks Project, More on Algebra, Tag 065H, lemma-relatively-pseudo-coherent,
the pseudo-coherent clause
(blueprint: lem-sfb-polynomial-presentation-pseudocoherence-invariance).
-/

@[expose] public section

universe uR uA v wA wP wQ

open CategoryTheory

namespace DerivedCategory

/-- Pseudo-coherence of a derived object after restriction of scalars is independent of
its finite polynomial presentation. Restriction is induced by the exact ordinary module
functor, so it keeps the additive groups and differentials of representing complexes.

Source: Stacks Project, More on Algebra, Tag 065H, lemma-relatively-pseudo-coherent,
the pseudo-coherent clause
(blueprint: lem-sfb-polynomial-presentation-pseudocoherence-invariance).

Proof: For a commutative ring B and b in B, evaluation B[t] → B has the exact finite free
resolution 0 → B[t] → B[t] → B → 0, with first map multiplication by t-b. Its kernel and
injectivity follow from division by the monic polynomial t-b, including over the zero ring.
Thus B[0] is pseudo-coherent over B[t]. The scalar-restriction equivalence of
lem-sfb-pseudocoherent-algebra-scalar-restriction (Stacks 064Z) says that restriction along
this evaluation preserves and reflects pseudo-coherence for every object of D(B).

Use the two surjections to lift the images of the y variables to polynomials f_j in P,
and the images of the x variables to polynomials g_i in Q. The common polynomial ring
T = R[x,y] evaluates to P by y_j ↦ f_j and to Q by x_i ↦ g_i. The two composite maps to A
agree on coefficients and variables, hence agree by the polynomial universal property.
Restriction of K along either composite therefore gives the same T-complex.

Starting with P, adjoin the y variables one at a time, acting by their chosen f_j.
The evaluation equivalence above at every step identifies pseudo-coherence over P with
pseudo-coherence of that T-complex. Starting with Q and adjoining the x variables acting
by g_i gives the same conclusion over Q. Combine the equivalences. Zero variables give
identity inductions. No boundedness, flatness, finite presentation or Noetherian hypothesis
is required. -/
theorem isPseudoCoherent_restrictScalars_polynomial_presentation_iff
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
    {r s : ℕ} (α : MvPolynomial (Fin r) R →ₐ[R] A)
    (β : MvPolynomial (Fin s) R →ₐ[R] A)
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA v} A)]
    [HasDerivedCategory.{wP} (ModuleCat.{max uR uA v} (MvPolynomial (Fin r) R))]
    [HasDerivedCategory.{wQ} (ModuleCat.{max uR uA v} (MvPolynomial (Fin s) R))]
    (K : DerivedCategory (ModuleCat.{max uR uA v} A)) :
    IsPseudoCoherent ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ↔
      IsPseudoCoherent ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K) := by
  sorry

end DerivedCategory
