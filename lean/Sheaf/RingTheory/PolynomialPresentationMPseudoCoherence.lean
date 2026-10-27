module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.RingTheory.RingPseudoCoherent

/-!
# Fixed-degree pseudo-coherence and finite polynomial presentations

Source: Stacks Project, More on Algebra, Tag 065H, lemma-relatively-pseudo-coherent,
equivalence of conditions (1) and (2) for a fixed integer m
(blueprint: lem-sfb-polynomial-presentation-m-pseudocoherence-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA v wA wP wQ

open CategoryTheory

namespace DerivedCategory

/-- For a fixed integer `m`, pseudo-coherence through degree `m` after restriction of
scalars is independent of the chosen finite polynomial presentation. The functor is
induced by ordinary exact restriction of module scalars: representing complexes keep
their additive groups and differentials, with scalar action through the presentation.

Source: Stacks Project, More on Algebra, Tag 065H, lemma-relatively-pseudo-coherent,
equivalence of conditions (1) and (2) for a fixed integer m
(blueprint: lem-sfb-polynomial-presentation-m-pseudocoherence-invariance).

Proof:
1. For every commutative ring B and b in B, evaluation e_b : B[t] → B has the exact
   sequence 0 → B[t] → B[t] → B → 0, where the first map multiplies by t-b.
   Constants give surjectivity. The identity t^a-b^a = (t-b)∑ t^(a-1-h)b^h gives
   the kernel calculation. The highest nonzero coefficient of a nonzero polynomial
   remains the coefficient in the next degree after multiplication by t-b, proving
   injectivity. The resulting complex in degrees -1 and 0 is a finite free model of
   B[0], which is therefore pseudo-coherent over B[t]. For B = 0 it is the zero sequence.
2. Apply lem-sfb-m-pseudocoherent-algebra-scalar-restriction (Stacks 064Z) to e_b.
   Step 1 supplies its pseudo-coherence hypothesis. For every L in D(B), restriction
   along e_b preserves and reflects m-pseudo-coherence with this same integer m.
3. Use the two surjections to lift β(y_j) to f_j in P and α(x_i) to g_i in Q.
   The polynomial universal property identifies T = R[x,y] both with P[y] and Q[x].
   Evaluation u : T → P at y_j = f_j and v : T → Q at x_i = g_i satisfies
   α ∘ u = β ∘ v = γ, since the composites agree on coefficients and all variables.
   Termwise restriction along either composite gives the identical T-action through γ,
   on the same additive groups with the same differentials.
4. Starting from P, adjoin y_1,...,y_s one at a time, acting by f_1,...,f_s. At each
   successor apply step 2 to evaluation at f_j, viewed in the preceding polynomial ring.
   Induction identifies m-pseudo-coherence of α_*K over P with that of γ_*K over T.
   Starting from Q and adjoining x_1,...,x_r acting by g_1,...,g_r gives the same result
   for β_*K. Combine the two equivalences. Zero variables give only the base case.
   No flatness, finite presentation, Noetherian or cohomological bound is used. -/
theorem isMPseudoCoherent_restrictScalars_polynomial_presentation_iff
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
    {r s : ℕ} (α : MvPolynomial (Fin r) R →ₐ[R] A)
    (β : MvPolynomial (Fin s) R →ₐ[R] A)
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA v} A)]
    [HasDerivedCategory.{wP} (ModuleCat.{max uR uA v} (MvPolynomial (Fin r) R))]
    [HasDerivedCategory.{wQ} (ModuleCat.{max uR uA v} (MvPolynomial (Fin s) R))]
    (m : ℤ) (K : DerivedCategory (ModuleCat.{max uR uA v} A)) :
    IsMPseudoCoherent m ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ↔
      IsMPseudoCoherent m ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj K) := by
  sorry

end DerivedCategory
