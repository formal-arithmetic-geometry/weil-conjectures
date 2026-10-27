module

public import Sheaf.RingTheory.MarkedFlatAlgebraDeformations
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Stability

/-! # Completion of marked flat algebra deformations

Source: Stacks Project, examples-defos.tex, Tag 0DYV (lemma-completion), and
algebra.tex, Tags 00MA and 0DYC (lemma-complete-modulo-nilpotent)
(blueprint: lem-sfb-adic-completion-flat-deformation-functor).

Base change uses the actual tensor product and its canonical simple-tensor formula.
All maps of completions are characterized on every ideal-power quotient, so neither
the special-fibre marking nor the base-change comparison is an arbitrary isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry.ArtinDeformation

namespace Algebra.FlatDeformation

/-- Completion gives a functor of marked flat deformation groupoids, preserves every
Artinian base change, and complete special fibres have automatically complete deformations.
The equivalences e identify the output algebras with their actual inverse-limit completions.
The finite-quotient conditions specify the canonical marking and every induced map.

Source: Stacks Project, Tag 0DYV; algebra.tex, Tags 00MA and 0DYC
(blueprint: lem-sfb-adic-completion-flat-deformation-functor).

Proof:
1. Set H = m_A Q. By lem-weil-pbc-artinian-local-noetherian-nilpotent it is finitely
generated and nilpotent. Its completion is Q, since Q/H^n is eventually Q. Apply
lem-weil-pbc-completion-noetherian-quotient-noetherian to infer Q is Noetherian.
Then lem-weil-pbc-adic-completion-noetherian and lem-weil-pbc-adic-completion-mod-ideal
give Noetherianity and completeness of its J_Q-adic completion. Flatness follows from
lem-weil-pbc-noetherian-completion-flat and lem-weil-pbc-flat-ring-map-comp.
2. The cyclic Q-module B has completion B-hat. The canonical tensor comparison of
lem-weil-pbc-completion-finite-module-tensor identifies Q-hat tensor_A k with B-hat.
At level n it sends u tensor b to u_n b. This is multiplicative and unital, giving
the canonical marking used in the conclusion.
3. Every test algebra A' is finite dimensional over k: choose finitely many generators
of its nilpotent maximal ideal, expand an element as a scalar plus those generators,
and iterate until the maximal-ideal power vanishes. The finitely many monomials span.
Thus A' is finite over A and Q tensor_A A' is finite over Q. By
lem-weil-pbc-flat-module-base-change it is flat over A', with special fibre B.
4. In Q' = Q tensor_A A', write L = J_Q Q' and H' = m_A' Q'. Its marked ideal
K is L + H'. If (H')^N = 0, expansion gives K^(n+N) contained in L^n contained
in K^n. The quotient maps and these cofinal inclusions identify the two completions,
by maps induced by the identity of Q'. Their composites are identity at every level.
5. Apply lem-weil-pbc-completion-finite-module-tensor to the finite Q-module Q'.
Together with step 4 it identifies Q-hat tensor_A A' with Q'-hat, canonically.
On simple tensors its nth coordinate is u_n tensor a'. A marked isomorphism acts
coordinatewise on completions. These formulas preserve products, units, markings,
identities and composition, giving the functors F. They give the unique j below.
Naturality and the identity/composition coherence for successive base changes follow
at each finite quotient from the same formula: u tensor a' tensor a'' maps to
u_n tensor (a' a''). Thus the resulting tensor isomorphism is the natural marked comparison.
6. If B is J-complete, apply lem-sfb-two-ideal-adic-completeness with first ideal
H (nilpotent, so Q is H-complete) and second ideal J_Q. It proves Q is J_Q-complete.
7. If B is local and J maximal, J_Q is maximal. Outside J_Q an element has an
inverse modulo H. Lift that inverse; the error is nilpotent and the finite geometric
series inverts one plus the error. Thus Q is local with exactly maximal ideal J_Q.
Combine steps 1 and 6 to get the final complete Noetherian local conclusion.
-/
theorem adicCompletion_flatDeformationFunctor
    (k B : Type u) [Field k] [CommRing B] [Algebra k B] [IsNoetherianRing B]
    (J : Ideal B) :
    (∀ (A : TestCategory k k) (Q : Groupoid B A),
      IsNoetherianRing (algebra Q) ∧
      IsNoetherianRing (AdicCompletion (ideal J Q) (algebra Q)) ∧
      ((algebraMap (algebra Q) (AdicCompletion (ideal J Q) (algebra Q))).comp
        (scalar Q).toRingHom).Flat ∧
      IsAdicComplete
        ((ideal J Q).map (algebraMap (algebra Q) (AdicCompletion (ideal J Q) (algebra Q))))
        (AdicCompletion (ideal J Q) (algebra Q)) ∧
      (IsAdicComplete J B →
        IsAdicComplete (ideal J Q) (algebra Q) ∧
        ∀ hB : IsLocalRing B, J = @IsLocalRing.maximalIdeal B _ hB →
          ∃ hQ : IsLocalRing (algebra Q),
            @IsLocalRing.maximalIdeal (algebra Q) _ hQ = ideal J Q)) ∧
    (∀ (A A' : TestCategory k k) (f : A ⟶ A') (Q : Groupoid B A),
      ∃ (Q' : Groupoid B A') (i : algebra Q →ₐ[k] algebra Q'), IsBaseChange f Q Q' i) ∧
    ∃ F : ∀ A : TestCategory k k, Groupoid B A ⥤ Groupoid (AdicCompletion J B) A,
      ∃ e : ∀ (A : TestCategory k k) (Q : Groupoid B A),
        algebra ((F A).obj Q) ≃ₐ[k] AdicCompletion (ideal J Q) (algebra Q),
      (∀ (A : TestCategory k k) (Q : Groupoid B A) (a : ring A),
        e A Q (scalar ((F A).obj Q) a) =
          algebraMap (algebra Q) (AdicCompletion (ideal J Q) (algebra Q)) (scalar Q a)) ∧
      (∀ (A : TestCategory k k) (Q : Groupoid B A),
        IsCompletionMap (ideal J Q) J (marking Q).toRingHom
          ((marking ((F A).obj Q)).toRingHom.comp (e A Q).symm.toRingHom)) ∧
      (∀ (A : TestCategory k k) (Q Q' : Groupoid B A) (f : Q ⟶ Q'),
        IsCompletionMap (ideal J Q) (ideal J Q') (hom f).toRingHom
          ((e A Q').toRingHom.comp
            ((hom ((F A).map f)).toRingHom.comp (e A Q).symm.toRingHom))) ∧
      (∀ (A A' : TestCategory k k) (f : A ⟶ A')
          (Q : Groupoid B A) (Q' : Groupoid B A') (i : algebra Q →ₐ[k] algebra Q'),
        IsBaseChange f Q Q' i →
          ∃! j : algebra ((F A).obj Q) →ₐ[k] algebra ((F A').obj Q'),
            IsBaseChange f ((F A).obj Q) ((F A').obj Q') j ∧
            IsCompletionMap (ideal J Q) (ideal J Q') i.toRingHom
              ((e A' Q').toRingHom.comp (j.toRingHom.comp (e A Q).symm.toRingHom))) := by
  sorry

end Algebra.FlatDeformation
