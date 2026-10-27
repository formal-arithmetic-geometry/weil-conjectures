/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.AlgebraicGeometry.TruncatedSectionConormalResidueKernel

/-! # Truncated polynomial sections imply smoothness

Source: Stacks Project, Algebra, Tag 02HT (lemma-smooth-test-artinian),
proof of (4) implies (1), after constructing sections of the truncated surjections.
(blueprint: lem-sfb-truncated-polynomial-sections-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Sections of every positive truncation of the localized square-zero polynomial
presentation imply smoothness on a principal neighbourhood of the chosen prime.
The ideal `J` is the kernel of the canonical localized presentation map; `hJ` names
this ideal without introducing a separate definition. The maximal ideal of the
localized polynomial ring is the extension of the inverse image of `q`.

Source: Stacks Project, Algebra, Tag 02HT (lemma-smooth-test-artinian),
proof of (4) implies (1), conormal differential and Artin--Rees paragraphs.
(blueprint: lem-sfb-truncated-polynomial-sections-smooth).

Proof in words, following the accepted six-step split:
1. Surjectivity of the finite polynomial presentation makes A finite type over R.
   By lem-weil-pbc-finite-type-noetherian-finite-presentation it is finitely presented.
   The polynomial ring and its prime localization C are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian.
   Thus J is finitely generated (def-weil-pbc-noetherian-ring). Put S = A_q, with
   maximal ideal n and residue field k (def-weil-pbc-localization-at-prime).
2. The localized polynomial algebra C is formally smooth: lift each variable
   across a square-zero ideal H, and lift denominators as units. If uv = 1 + h,
   h in H, then uv(1-h) = 1. Use def-weil-pbc-formally-smooth-adic and
   def-weil-pbc-mv-polynomial-ring. The polynomial differential basis and its
   localization identify Omega(C/R) with C^d by
   lem-weil-pbc-polynomial-ring-kahler-basis and
   lem-weil-pbc-kahler-differentials-localization.
3. Apply lem-weil-pbc-artin-rees to J inside C and the maximal ideal m. For its
   bound c, choose N = c+2. Then m^N intersect J is contained in m^2 J, hence mJ.
   Use the section at this N; compatibility of the different sections is unnecessary.
4. Set M = J/J^2 and T = S tensor_C Omega(C/R), with conormal differential delta.
   The lemma lem-weil-pbc-truncated-section-conormal-residue-kernel gives
   delta(x) in nT implies x in nM, so M/nM -> T/nT is injective. The maps
   [r] tensor x -> [rx] and [x] -> 1 tensor x identify k tensor_S U with U/nU
   and carry k tensor delta to this map (def-weil-module-base-change).
5. Apply lem-sfb-formally-smooth-local-residue-conormal: S is local, J finitely
   generated, C formally smooth, Omega(C/R) finite free, and the residue
   conormal map injective. Conclude formal smoothness of S over R.
6. Apply lem-sfb-formally-smooth-prime-neighbourhood using finite presentation
   of A over R and formal smoothness of A_q. Obtain g outside q with A_g smooth.
The argument includes d = 0, N = 1 in the hypothesis, and the case J = 0.
-/
theorem exists_smooth_away_of_truncated_polynomial_sections
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing R]
    (d : ℕ) (α : MvPolynomial (Fin d) R →ₐ[R] A) (hα : Function.Surjective α)
    (q : Ideal A) [q.IsPrime]
    (J : Ideal (Localization.AtPrime (q.comap α.toRingHom)))
    (hJ : J = RingHom.ker
      (Localization.localAlgHom (q.comap α.toRingHom) q α rfl).toRingHom)
    (hsections : ∀ (N : ℕ), 1 ≤ N →
      ∃ σ :
        (Localization.AtPrime (q.comap α.toRingHom) ⧸
          (J ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap α.toRingHom)) ^ N))
          →ₐ[R]
        (Localization.AtPrime (q.comap α.toRingHom) ⧸
          (J ^ 2 ⊔
            IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap α.toRingHom)) ^ N)),
        (Ideal.Quotient.factorₐ R
          (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
            AlgHom.id R _) :
    ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) := by
  sorry

end Algebra
