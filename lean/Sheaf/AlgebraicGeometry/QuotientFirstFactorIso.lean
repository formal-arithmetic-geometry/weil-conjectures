/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-! # Identification of a quotient factor over an isomorphism locus

Source: Stacks Project, More on Algebra, proof of Tag 09XH.
(blueprint: lem-weil-pbc-quotient-first-factor-iso)
-/

@[expose] public section

universe u w z

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- An idempotent factor supported in the isomorphism locus is preserved isomorphically.

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Tag 09XH,
including the localization and final quotient argument.
(blueprint: lem-weil-pbc-quotient-first-factor-iso).

Split S'/J' by the idempotent c as C'₁ = (S'/J')/(1-c) and C'₂ = (S'/J')/(c),
using the Chinese remainder theorem. The equality f(c)=e.symm(1,0) makes f diagonal
on these products and gives ring maps to D₁ and D₂. It remains to prove that the
first map is an isomorphism. Let t lift c and K'=J'+(1-t). Its zero locus is the
first factor and is contained in U. Write the complement of U as V(L). Since
V(L) and V(K') are disjoint, L+K'=S'; choose 1=l+k with l in L and k in K'.
Put g=t*l. Idempotence gives g-t in J', and g in L gives D(g) contained in U.
The scheme isomorphism on U identifies the section rings on D(g), which are the
localizations S'_g and S_{i(g)}, with the canonical localization map induced by i.
Quotient this ring isomorphism by the extensions of K'=J'+(1-g) and
K=J+(1-i(g)). These ideals correspond because J=map i J'. Since g becomes 1
in each quotient, the localization quotients are S'/K' and S/K respectively.
These are precisely C'₁ and D₁, and the resulting isomorphism is the first map.
The second factor map is the map already induced by f. -/
theorem quotient_firstFactor_equiv_of_restrict_iso
    {S' S : Type u} [CommRing S'] [CommRing S] (i : S' →+* S)
    (J' : Ideal S') (J : Ideal S) (hJ : Ideal.map i J' = J)
    (f : (S' ⧸ J') →+* (S ⧸ J))
    (hf : ∀ b, f (Ideal.Quotient.mk J' b) = Ideal.Quotient.mk J (i b))
    {D₁ : Type w} {D₂ : Type z} [CommRing D₁] [CommRing D₂]
    (e : (S ⧸ J) ≃+* D₁ × D₂) (c : S' ⧸ J') (hc : IsIdempotentElem c)
    (hfc : f c = e.symm (1, 0)) (U : (Spec (.of S')).Opens)
    (hiso : IsIso (Spec.map (CommRingCat.ofHom i) ∣_ U))
    (hU : PrimeSpectrum.comap (Ideal.Quotient.mk J') ''
      (PrimeSpectrum.basicOpen c : Set _) ⊆ U.1) :
    ∃ (D'₁ D'₂ : Type u) (_ : CommRing D'₁) (_ : CommRing D'₂)
      (e' : (S' ⧸ J') ≃+* D'₁ × D'₂) (g : D'₁ ≃+* D₁) (h : D'₂ →+* D₂),
      e' c = (1, 0) ∧
      ∀ r : S' ⧸ J', e (f r) = (g (e' r).1, h (e' r).2) := by
  sorry

end AlgebraicGeometry
