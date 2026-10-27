module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Lie.Free
import Sheaf.Algebra.Lie.ArbitraryBasisPBW

/-!
# The free rational Lie algebra embeds in the associative word algebra

Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, printed p.504;
the supporting embedding argument uses Section 10j, Theorem 10.36, pp.199–200.
(blueprint: lem-sfb-free-lie-word-embedding)

`FreeLieAlgebra ℚ I` has generators `FreeLieAlgebra.of ℚ` and the universal property
`FreeLieAlgebra.lift`. The associative word algebra is `FreeAlgebra ℚ I`, whose
`FreeAlgebra.equivMonoidAlgebraFreeMonoid` identifies its multiplication with word
concatenation, including the empty word. Its one-letter words are `FreeAlgebra.ι ℚ`.
The target Lie ring structure is passed explicitly and is the commutator structure.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace FreeLieAlgebra

/-- The unique Lie homomorphism taking each free generator to its one-letter word
is injective, including for an empty finite alphabet.
Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, printed p.504;
Section 10j, Theorem 10.36, printed pp.199–200 supplies the supporting PBW input.
(blueprint: lem-sfb-free-lie-word-embedding)

Proof plan:
1. Form the tensor-algebra quotient `U = UniversalEnvelopingAlgebra ℚ (FreeLieAlgebra ℚ I)`
   and its canonical Lie homomorphism `j = UniversalEnvelopingAlgebra.ι ℚ`, as in
   `lem-sfb-enveloping-universal-property`. The arbitrary-dimensional rational PBW
   theorem `lem-sfb-arbitrary-basis-pbw` makes `j` injective. No finite-dimensionality
   assumption on the free Lie algebra is used.
2. Evaluate an associative word in `U` by multiplying the images `j (of ℚ i)` of
   its letters, sending the empty word to one. The universal property
   `FreeAlgebra.lift` gives this unital rational algebra homomorphism `p`.
   Concatenation makes it multiplicative; hence it also preserves commutators.
3. The Lie homomorphisms `p ∘ q` and `j` agree on generators. Uniqueness in
   `FreeLieAlgebra.lift` makes them equal. Apply `p` to an equality `q x = q y`
   and use injectivity of `j` to obtain `x = y`. For an empty alphabet the same
   uniqueness makes the identity and zero endomorphisms equal, so the source
   is zero and the word algebra is rational scalars. The argument still applies.
-/
theorem lift_freeAlgebra_injective (I : Type u) [Finite I] :
    Function.Injective
      (@FreeLieAlgebra.lift ℚ I _ (FreeAlgebra ℚ I)
        LieRing.ofAssociativeRing _ (FreeAlgebra.ι ℚ)) := by
  sorry

end FreeLieAlgebra
