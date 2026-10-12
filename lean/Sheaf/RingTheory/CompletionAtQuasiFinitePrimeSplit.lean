module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Sheaf.RingTheory.CompletionFiniteExtension

/-!
# A completion factor from a finite subalgebra agreeing away from an element

Source: Stacks Project, Algebra, proof of Lemma Tag 07NC after choosing the finite
subalgebra (blueprint: lem-weil-pbc-completion-finite-subalgebra-away-split).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite subalgebra agreeing away from an element gives a direct completion factor.
Source: Stacks Project, Algebra, proof of Lemma Tag 07NC, after the choice of the
finite subalgebra (blueprint: lem-weil-pbc-completion-finite-subalgebra-away-split).

Proof: put q' = q ∩ S'. Since g is outside q and the localized inclusion is
bijective, clearing powers of g identifies S' localized at q' with S localized
at q: write each numerator and denominator as an element of S' after multiplying
by a power of g; the same operation proves injectivity. This isomorphism carries
the maximal ideals and their powers to each other, hence induces a ring
isomorphism α of completions, compatible with the quotient evaluations.
Apply `AdicCompletion.completion_finite_extension` to S'. Its product equivalence
has a factor for q'. The associated idempotent e in T = Rph ⊗[R] S' has eT
isomorphic to the completion at q'. The image γ = 1 ⊗ g is a unit on this
factor, because g is outside q'; choose v supported on e with vγ = e.
The tensor inclusion j : T → U becomes an isomorphism after inverting γ, by
localization commuting with tensor product and the assumed bijective away map.
Let f₀ = j(e) and w = j(v). The restriction j : eT → f₀U is bijective.
For injectivity, an element in its kernel is killed by a power of γ and
multiplication by the same power of v kills the denominator and recovers it.
For surjectivity, write u/1 = j(t)/γ^k in the localized ring. For some l,
γ^(k+l)u = γ^l j(t) in U (here γ denotes its image in U). Multiplying
by f₀ and w^(k+l) gives uf₀ = j(v^(k+l) γ^l t e), which lies in the image.
The inverse on eT exists because vγ = e there; these formulas also cover
k = 0 or l = 0.
The given ψ agrees with the completed local map on every coordinate, because
it has the levelwise formula and evaluations are surjective on quotient classes.
It therefore agrees with α composed with the finite factor's completed-base map.
This equality also implies compatibility with the R-action. The universal
property of the tensor product constructs φ(x ⊗ y) = ψ(x)ι(y). On T this is
α composed with the q' projection: check on pure tensors using compatibility
with S' and the completed base in the finite-extension decomposition.
Consequently φ is an isomorphism on f₀U and vanishes on (1-f₀)U. Take
B = (1-f₀)U with unit 1-f₀ and β(u) = (1-f₀)u. The idempotent product
decomposition, composed with the isomorphism on f₀U, is the required ring
equivalence, whose first component is exactly φ. -/
theorem completion_split_of_finite_subalgebra_away
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (q : PrimeSpectrum S)
    (S' : Subalgebra R S) [Module.Finite R S']
    (g : S') (hg : g.1 ∉ q.asIdeal)
    (haway : Function.Bijective (Localization.awayMap S'.val.toRingHom g)) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let U := TensorProduct R Rph S
    ∀ (ψ : Rph →+* Sqh),
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) →
      ∃ (B : Type (max u v)) (_ : CommRing B) (β : U →+* B) (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S),
          φ (TensorProduct.tmul R x y) =
            ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) ∧
        ∃ e : U ≃+* Sqh × B, e.toRingHom = RingHom.prod φ β := by
  sorry

end Algebra
