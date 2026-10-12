/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Reduction of the completed module along an extended ideal

Source: Stacks Project, Algebra, Lemma Tag 0394, proof after identifying the two
completions; Lemma Tag 05GG.
(blueprint: lem-weil-pbc-extended-completion-module-reduction).
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- The reduction of the completion for an extended ideal is finite over the reduced
completed base when the original reduction is finite.
Source: Stacks Project, Algebra, Lemma Tag 0394, last paragraph of the proof, with the
hypotheses of Tag 031D verified using Tag 05GG.
(blueprint: lem-weil-pbc-extended-completion-module-reduction).

Proof:
1. Give `S` its `R`-module structure via `φ`, and put `J = Ideal.map φ I`. The ideals
   `J ^ k` equal `Ideal.map φ (I ^ k)`. Consequently `J ^ k` as an `R`-submodule of
   `S` is `I ^ k • ⊤`. The quotient maps identify the two inverse limits, so
   `AdicCompletion J S` is the completion of the `R`-module `S` for `I`.
2. The coordinate hypothesis determines `ψ` uniquely, since every residue class has a
   representative and evaluations are jointly injective. Componentwise multiplication
   then identifies its action with the canonical completed-base action on the module
   completion. In particular restriction along `R → AdicCompletion I R` agrees with
   the original action. For `K = I AdicCompletion I R`, expanding the generators of
   the extended ideal gives `K ^ k • ⊤ = I ^ k • ⊤` after restriction of scalars.
3. Tag 05GG applied to the `R`-module `S`, with `I` finitely generated, makes that
   completion complete and identifies its reduction modulo `I` with `S/J`, by the
   surjective first evaluation whose kernel is `I • ⊤`. Step 2 identifies
   reduction by `K` with this same quotient, including its scalar action.
4. Tag 05GG for `R` identifies `AdicCompletion I R / K` with `R/I`. Together with
   step 3 and the component formula for `ψ`, this identifies the quotient module and
   its scalar action with `S/J` over `R/I`. Transport the given finite family of
   generators across these identifications to obtain the asserted finiteness.

Edge cases: `I = ⊤` gives zero completions and zero quotient modules; `I = ⊥` gives
`R` and `S` themselves and the given finiteness hypothesis. No local or Noetherian
hypothesis is used. -/
theorem extendedCompletion_module_reduction
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) (hI : I.FG)
    (hfinite : letI := (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).toAlgebra
      Module.Finite (R ⧸ I) (S ⧸ Ideal.map φ I))
    (ψ : AdicCompletion I R →+* AdicCompletion (Ideal.map φ I) S)
    (hψ : ∀ (k : ℕ) (x : AdicCompletion I R) (r : R),
      AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r →
      AdicCompletion.evalₐ (Ideal.map φ I) k (ψ x) =
        Ideal.Quotient.mk ((Ideal.map φ I) ^ k) (φ r)) :
    letI := ψ.toAlgebra
    let K := I.map (algebraMap R (AdicCompletion I R))
    Module.Finite (AdicCompletion I R ⧸ K)
        (AdicCompletion (Ideal.map φ I) S ⧸
          (K • ⊤ : Submodule (AdicCompletion I R) (AdicCompletion (Ideal.map φ I) S))) := by
  sorry

end AdicCompletion
