module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.RingTheory.CompleteIntersectionOverField
import Sheaf.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

@[expose] public section

universe u v
namespace Algebra

/-- Transport of a complete-intersection fibre witness across principal localization,
for a fixed prime `q₁` contracting to `q`.

Source: Stacks Project, Algebra, Tag 00SY, first sentence of (3) ⇒ (2), and Tag 00SA (1).
(blueprint: lem-weil-pbc-syntomic-principal-localization-fibre-transport).

Proof: put `p = q ∩ R`, `k = κ(p)`, `F = k ⊗[R] S`, and `a = 1 ⊗ g`.
The scalar tower and the contraction equality give `q₁ ∩ R = p`, identifying the two
base residue fields as `k`. Base change of principal localization identifies the new
fibre `F₁ = k ⊗[R] S_g` with `F_a`: denominators are powers of `a` and the map
`φ : F → F₁` sends `x ⊗ s` to `x ⊗ (s/1)`.

The prime-local rings `S_q` and `(S_g)_{q₁}` are canonically isomorphic, since both
invert exactly the elements of `S` outside `q`. Their residue fields are therefore
isomorphic, compatibly with the maps from `S` and `k`. Consequently the map from `F₁`
to `κ(q₁)` composed with `φ` is the map from `F` to `κ(q)` followed by this field
isomorphism. Taking kernels shows that the canonical fibre primes satisfy
`φ⁻¹(Q₁) = Q`. Choose the witness `h` from `hci` and set `h₁ = φ(h)`.
It is outside `Q₁` because `h` is outside `Q`.

The localization `(F₁)_{h₁}` is a `k`-algebra isomorphic to `(F_h)_{a/1}`:
both have the universal property of inverting `a` and `h` in `F`. The given `F_h`
is a global complete intersection, so its principal localization at `a/1` is one
by Tag 00SA (1). Transport this conclusion along the `k`-algebra isomorphism:
the zero-ring clause is preserved; otherwise compose the polynomial-quotient
presentation with the isomorphism and use its homeomorphism on prime spectra to
preserve Krull dimension. This supplies the required witness `h₁`. -/
theorem exists_completeIntersection_fibre_transport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (g : S) (hg : g ∉ q.asIdeal)
    (q₁ : PrimeSpectrum (Localization.Away g))
    (hq : q₁.comap (algebraMap S (Localization.Away g)) = q)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ h : (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).Fiber
          (Localization.Away g),
        h ∉ (PrimeSpectrum.preimageEquivFiber R (Localization.Away g)
          (q₁.comap (algebraMap R (Localization.Away g))) ⟨q₁, rfl⟩).asIdeal ∧
        IsGlobalCompleteIntersection
          (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).ResidueField
          (Localization.Away h) := by
  sorry

end Algebra
