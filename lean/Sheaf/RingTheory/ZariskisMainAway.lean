module

public import Mathlib.RingTheory.ZariskisMainTheorem
public import Sheaf.RingTheory.QuasiFiniteAtPrime

@[expose] public section

universe u v

namespace Algebra

/-! # Zariski's main theorem, integral closure localization
Source: literature/stacks-project/algebra.tex, Algebra, Theorem Tag 00Q9
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away)
-/

/-- Zariski's main theorem for a finite type algebra, at a quasi-finite prime.
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away)
Proof follows Stacks Tag 00Q9.  Write `R = A`, `S = B`, and `S'` for the
integral closure.  For the claim `P(n)` assume that `S` is finite over
`R[x₁, ..., xₙ]`, and induct on `n`.  For `n = 0`, finite generation makes
every element integral, so `S' = S` and `h = 1`.  First, the integral closure
is integrally closed: an element integral over it is integral over the base by
finite generation and transitivity.  For `n = 1`, replace the base by `S'`;
finite type and quasi-finiteness persist.  With `C = R[x]`, use the conductor
`J = {s | sS ⊆ C}`.  The conductor radical coefficient lemma makes the image
of `x` strongly transcendental after quotienting by `√J`; the reduced strongly
transcendental lemma and the four-rings lemma give `s ∈ J \ q`.  Then
`C_s → S_s` is an isomorphism, quasi-finiteness passes to `C`, and the
monogenic Zariski main theorem gives `h ∈ R \ q` with `R_h ≅ C_h`.
Surjectivity expresses `s/1` over this localization; replacing `h` by a
product identifies the principal localizations and yields `R_h ≅ S_h`.
For `n ≥ 2`, take the integral closure `R'` of `R[x₁, ..., xₙ₋₁]`, apply
the `n = 1` case to `R' → S`, and choose a finite subalgebra `R''` generated
by the resulting denominators and lifts of algebra generators.  The localized
map `R''_{g'} → S_{g'}` is an isomorphism and quasi-finiteness descends to
`R → R''`.  Apply `P(n−1)`, combine the two denominators, and use the
localization identities.  The resulting element lies in `S'`, and injectivity
and surjectivity of the composite give the required bijective `awayMap`.
-/
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hq : IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩) :
    ∃ h : integralClosure R S, h.1 ∉ q ∧
      Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom h) := by
  sorry

end Algebra
