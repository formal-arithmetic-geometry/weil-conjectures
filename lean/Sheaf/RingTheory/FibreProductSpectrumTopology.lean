module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Topology of the spectrum of a ring fibre product

Source: Stacks Project, Tag 0B7J, `lemma-points-of-fibre-product`, in
`situation-module-over-fibre-product` (blueprint: lem-sfb-fibre-product-spectrum-topology).
-/

@[expose] public section

set_option autoImplicit false

universe uA uD uT uH

namespace PrimeSpectrum

/-- Joint surjectivity and continuous descent for the spectrum of the matching-pairs ring.
`RingHom.pullback α β` is the subring of `A × T` defined by `α a = β t`, with its
componentwise operations, and `pullbackFst`, `pullbackSnd` are its projections.
The prime spectra here are the underlying Zariski spaces of `AlgebraicGeometry.Spec`.

Source: Stacks Project, Tag 0B7J, `lemma-points-of-fibre-product`
(blueprint: lem-sfb-fibre-product-spectrum-topology).

Proof plan (the nine steps of the node):
1. Put I = ker α and K = ker (P → T). Surjectivity of α makes P → T surjective.
   The square commutes, and contraction pulls a basic open D(b) back to D(f(b))
   (`def-weil-affine-spectrum`).
2. For c ∈ I, put e = (c,0). The localized projection P_e → A_c is an isomorphism:
   a/c^n lifts to (ca,0)/e^(n+1); if c^k a = 0, then e^(k+1)(a,t) = 0.
   These fraction computations use `def-weil-ring-localization-away`.
3. The quotient-spectrum theorem identifies Spec T with V(K), and Spec D with V(I)
   (`lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`). Step 2 and the
   principal-localization theorem (`lem-weil-pbc-spec-localization-away-basic-open`)
   identify D_A(c) with D_P((c,0)). These cover the complement of V(K), proving
   joint surjectivity.
4. Contraction gives i⁻¹(V(K)) = V(I). Outside V(K) the lift in Spec A is unique.
   Over V(K), the lift in Spec T is unique. An equality i(y) = j(z) arises from
   d ∈ Spec D with r(d) = y and s(d) = z, by the quotient-spectrum theorem.
5. Define h using a lift in either spectrum. Compatibility of u and v, together
   with step 4, makes it independent of the lift. Joint surjectivity gives uniqueness.
6. To prove the topology criterion, suppose W has open inverse images U and V.
   For z ∈ V choose D_T(t) ⊆ V and a lifting β(t). Write Spec A ∖ U = V(J).
   Compatibility on Spec D gives V(I) ∩ V(J) ⊆ V(a), using the principal-open
   basis and quotient-spectrum theorem from step 3.
7. The radical-as-intersection theorem (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`)
   gives a^n = c + b with n ≥ 1, c ∈ I, b ∈ J. The pair p = (ab,t^(n+1)) lies
   in P. Its basic open contains j(z); its two inverse images lie in U and V.
   Joint surjectivity implies D_P(p) ⊆ W, giving neighbourhoods on V(K).
8. For x ∈ W outside V(K), lift to y ∈ U, choose c ∈ I outside y and D_A(a) ⊆ U
   containing y. Then D_P((ca,0)) contains x, has inverse images in U and V, and
   lies in W by joint surjectivity. Hence W is open.
9. Apply steps 6–8 to W = h⁻¹(O) for each open O in H. Its inverse images are
   open by continuity of u and v, so h is continuous. Step 5 proves unique descent.
   Empty spectra require choices only at existing points and satisfy the same property.
-/
theorem pullback_jointly_surjective_and_existsUnique_continuousMap
    {A : Type uA} {D : Type uD} {T : Type uT}
    [CommRing A] [CommRing D] [CommRing T]
    (α : A →+* D) (β : T →+* D) (hα : Function.Surjective α) :
    (∀ p : PrimeSpectrum (α.pullback β),
      (∃ a : PrimeSpectrum A, comap (α.pullbackFst β) a = p) ∨
      (∃ t : PrimeSpectrum T, comap (α.pullbackSnd β) t = p)) ∧
    ∀ (H : Type uH) [TopologicalSpace H]
      (u : C(PrimeSpectrum A, H)) (v : C(PrimeSpectrum T, H)),
      u ∘ comap α = v ∘ comap β →
      ∃! h : C(PrimeSpectrum (α.pullback β), H),
        h ∘ comap (α.pullbackFst β) = u ∧ h ∘ comap (α.pullbackSnd β) = v := by
  sorry

end PrimeSpectrum
