/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Fixed-residue lifts give truncated sections

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), paragraphs
"Let N" and "Applying condition (4)"
(blueprint: lem-sfb-fixed-residue-lifts-truncated-section).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Algebra

/-- Fixed-residue length-one lifting tests give sections of truncated extensions.

Source: literature/stacks-project/algebra.tex, Tag 02HT, proof of (4) implies (1),
paragraphs "Let N" and "Applying condition (4)".
(blueprint: lem-sfb-fixed-residue-lifts-truncated-section).

Proof in words:
1. Put S = A_q, k = its residue field, J = ker p, m = maximalIdeal C, and
n = maximalIdeal S. Surjectivity of p gives p⁻¹(n) = m, J ≤ m and p(m) = n.
For N ≥ 1 put I = J² + m^N, L = J + m^N, E = C/I and F = C/L.
Both ideals lie between m^N and m. The Noetherian local quotient lemma
(lem-weil-pbc-noetherian-local-quotient-artinian-local) makes E and F nonzero
Artinian local with N-nilpotent maximal ideals. Quotient representatives give
F = S/n^N, since p(m^N) = n^N. Their residue fields identify canonically with
C/m = S/n = k, and E → F induces the identity under these identifications.
2. Filter K = ker(E → F) by ideals 0 = K₀ ≤ ⋯ ≤ Kᵣ = K whose successive
quotients have E-module length one, using
lem-weil-pbc-artinian-ideal-length-one-filtration. Each Dᵢ = E/Kᵢ is a quotient
C/Hᵢ with m^N ≤ Hᵢ ≤ m; the same quotient lemma gives nonzero Artinian local
rings with specified residue field k. Every Dᵢ → Dᵢ₊₁ is the identity on residues.
3. The kernel Kᵢ₊₁/Kᵢ has length one also over Dᵢ, since restriction along
E → Dᵢ identifies its submodule lattices (def-weil-pbc-module-length). Start
with A → S → F = Dᵣ and apply hlift down the filtration. At every step use the
structural R-map into Dᵢ. The resulting maps remain R-compatible, have the
canonical residue composite A → k, and lift the initial map to F. At the end
obtain a' : A → E. For r = 0 the initial map already is the required lift.
4. For s outside q, a'(s) has nonzero residue and is a unit by
lem-weil-pbc-local-ring-unit-criterion. Extend a' to b : S → E by
b(x/s) = a'(x)/a'(s) (def-weil-pbc-localization-at-prime). Applying a' to the
fraction relation and cancelling the unit from its extra denominator proves
well-definedness. The fraction operations prove that b is a ring map; its
values on R prove R-compatibility. Its composite with E → F equals S → F,
since both maps agree on A and hence on all fractions.
5. The image of n under b lies in the maximal ideal of E, whose Nth power is
zero. Thus b kills n^N and descends to an R-algebra map σ : F → E. Composing
with E → F gives the identity after the surjection S → F, and hence on F.
For N = 1 both quotients are C/m; for J = 0 the quotient map is the identity.

For tests in the displayed larger universe, use ULift ring equivalences for
the intermediate quotients, transporting their residue identifications as
well. Locality, Artinianness, kernel length and all map equalities are preserved.
No hypothesis of finite type, a residue characteristic, or a choice of residue
field different from the specified k is needed. -/
theorem fixed_residue_lifts_truncated_section
    {R : Type u} {A : Type v} {C : Type w}
    [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (q : Ideal A) [q.IsPrime] [IsNoetherianRing C] [IsLocalRing C]
    (p : C →ₐ[R] Localization.AtPrime q) (hp : Function.Surjective p)
    (hlift : ∀ (B' B : Type (max u v w t)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (e' : IsLocalRing.ResidueField B' ≃+* q.ResidueField)
        (e : IsLocalRing.ResidueField B ≃+* q.ResidueField),
        e'.toRingHom.comp (IsLocalRing.residue B') =
          (e.toRingHom.comp (IsLocalRing.residue B)).comp φ →
        ∀ (ρ : R →+* B') (a : A →+* B),
          a.comp (algebraMap R A) = φ.comp ρ →
          (e.toRingHom.comp (IsLocalRing.residue B)).comp a =
            algebraMap A q.ResidueField →
          ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∀ (N : ℕ), 1 ≤ N →
      ∃ σ : (C ⧸ (RingHom.ker p.toRingHom ⊔ IsLocalRing.maximalIdeal C ^ N)) →ₐ[R]
          (C ⧸ (RingHom.ker p.toRingHom ^ 2 ⊔ IsLocalRing.maximalIdeal C ^ N)),
        (Ideal.Quotient.factorₐ R
          (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
            AlgHom.id R _ := by
  sorry

end Algebra
