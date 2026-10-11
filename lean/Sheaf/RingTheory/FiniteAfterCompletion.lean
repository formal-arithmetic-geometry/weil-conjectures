import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite modules after completion

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0394
(blueprint: lem-weil-pbc-finite-after-completion).
-/

universe u v

namespace AdicCompletion

/--
For a local homomorphism of local rings whose maximal ideals are finitely generated and whose
special fibre is finite-dimensional, the completion of the target is the completion for the
extended maximal ideal and is finite over the completion of the source.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0394
(blueprint: lem-weil-pbc-finite-after-completion).
Proof (following the seven steps of the node):
1. The special fibre is Artinian by lem-weil-pbc-finite-dim-algebra-artinian and local;
   lem-weil-pbc-artinian-local-unique-prime makes n the only prime above mS.
2. By lem-weil-pbc-zero-locus-eq-iff-radical-eq its radical is n; then
   lem-weil-pbc-fg-ideal-radical-power gives n^t ≤ mS for some t ≥ 1.
3. The powers of mS are the extended powers of m. Together with mS ≤ n, this gives
   the canonical comparison isomorphism by lem-weil-pbc-change-ideal-completion.
4. Regard S' as the completion of the R-module S. Its canonical R-completion action
   agrees, through γ and componentwise comparison, with the action through φhat.
5. By lem-weil-pbc-module-completion-complete and lem-weil-pbc-adic-completion-mod-ideal,
   S' and R-completion are complete, and their quotients modulo m are S/mS and R/m.
6. Powers of the extended ideal act as powers of m. Thus S' is separated for that
   ideal, and its quotient is the given finite-dimensional special fibre.
7. Apply lem-weil-pbc-finite-over-complete-ring to S' over R-completion; transport
   finite generation along the comparison isomorphism from step 4.
-/
theorem finite_after_completion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (m : Ideal R) (n : Ideal S) (φ : R →+* S)
    (hm : m = IsLocalRing.maximalIdeal R)
    (hn : n = IsLocalRing.maximalIdeal S)
    [IsLocalHom φ]
    (hm_fg : m.FG) (hn_fg : n.FG)
    (hfinite : letI := (Ideal.quotientMap (Ideal.map φ m) φ Ideal.le_comap_map).toAlgebra
      Module.Finite (R ⧸ m) (S ⧸ Ideal.map φ m)) :
    ∃ (γ : AdicCompletion (Ideal.map φ m) S ≃+* AdicCompletion n S)
      (φhat : AdicCompletion m R →+* AdicCompletion n S),
      (∀ (k : ℕ) (x : AdicCompletion (Ideal.map φ m) S) (s : S),
        AdicCompletion.evalₐ (Ideal.map φ m) k x =
          Ideal.Quotient.mk ((Ideal.map φ m) ^ k) s →
        AdicCompletion.evalₐ n k (γ x) = Ideal.Quotient.mk (n ^ k) s) ∧
      (∀ (k : ℕ) (x : AdicCompletion m R) (r : R),
        AdicCompletion.evalₐ m k x = Ideal.Quotient.mk (m ^ k) r →
        AdicCompletion.evalₐ n k (φhat x) = Ideal.Quotient.mk (n ^ k) (φ r)) ∧
      letI := φhat.toAlgebra
      Module.Finite (AdicCompletion m R) (AdicCompletion n S) := by
  sorry

end AdicCompletion
