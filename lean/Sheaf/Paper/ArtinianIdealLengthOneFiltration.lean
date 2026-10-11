module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length

/-!
# Length-one filtrations of ideals in Artinian rings

Source: literature/stacks-project/algebra.tex, Algebra, proof of Lemma Tag 02HT
(blueprint: lem-weil-pbc-artinian-ideal-length-one-filtration).
-/

@[expose] public section

universe u

namespace RingTheory

/--
For an Artinian commutative ring, every ideal admits a finite filtration by ideals
whose successive quotients have module length one.

Source: literature/stacks-project/algebra.tex, Algebra, proof of Lemma Tag 02HT
(blueprint: lem-weil-pbc-artinian-ideal-length-one-filtration). The proof uses
`lem-weil-pbc-artinian-ring-self-finite-length` and
`lem-weil-pbc-finite-length-module-simple-filtration`. Regard `B` as a module over
itself and use the Artinian-ring finite-length lemma to bound strict submodule
chains. The ideal `J` is a submodule of `B`, so it has finite length. Apply the
finite-length simple-filtration lemma to `J`; its submodules are precisely the
ideals contained in `J`, and its successive module quotients are the displayed
quotients. The zero ideal is handled by taking `r = 0`.
-/
theorem exists_ideal_filtration_length_one (B : Type u) [CommRing B]
    [IsArtinianRing B] (J : Ideal B) :
    ∃ (r : ℕ) (F : Fin (r + 1) → Ideal B),
      F 0 = ⊥ ∧ F (Fin.last r) = J ∧
        (∀ i : Fin r, F (Fin.castSucc i) ≤ F i.succ) ∧
        (∀ i : Fin r,
          Module.length B
              (↥(F i.succ) ⧸
                Submodule.comap (F i.succ).subtype (F (Fin.castSucc i))) = 1) := by
  sorry

end RingTheory
