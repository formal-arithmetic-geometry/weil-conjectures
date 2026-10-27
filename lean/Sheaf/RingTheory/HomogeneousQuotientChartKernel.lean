/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q72
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.GroupTheory.MonoidLocalization.Away

/-! # Kernel of a homogeneous quotient on a degree-one chart

Source: Stacks Project, constructions.tex, Tags 03GL and 01MY, homogeneous fractions
in the ideal of a closed projective subscheme and the induced chart map.
(blueprint: lem-sfb-homogeneous-quotient-chart-kernel)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace HomogeneousLocalization

/-- The quotient grading, surjective chart map, its homogeneous-fraction kernel,
and the canonical quotient isomorphism, including zero and nilpotent denominators.
Source: Stacks Project, constructions.tex, Tag 03GL, proof of
lemma-closed-in-projective-space, and Tag 01MY, lemma-morphism-proj (2).
(blueprint: lem-sfb-homogeneous-quotient-chart-kernel)

Proof:
1. The images of the homogeneous pieces span the quotient. If a finite sum of
   homogeneous lifts lies in K, homogeneity puts each component in K. Hence their
   images form a direct grading; the unit and multiplication descend as well.
2. Define the chart map on fractions by s/f^d ↦ [s]/[f]^d. The ordinary
   localization relation f^k(s*f^e-t*f^d)=0 descends under the quotient map,
   proving well-definedness. The fraction formulas prove that it is a ring map.
   These are the constructions of def-nagata-homogeneous-localization-degree-zero
   and def-weil-ring-localization-away.
3. Every homogeneous quotient numerator has a homogeneous lift, proving
   surjectivity, even when the image of f is zero.
4. Every displayed generator is killed. Conversely, if s/f^d maps to zero, the
   localization relation gives f^n*s ∈ K for some n. This numerator has degree
   n+d, and s/f^d = (f^n*s)/f^(n+d), a displayed generator. Thus ker q = J.
5. Descend q to the quotient by J. Surjectivity is inherited; equality of images
   means the difference lies in ker q = J, proving injectivity. The resulting
   ring isomorphism sends every quotient class to q of its representative.
   No cancellation or nonzero hypothesis is used. For nilpotent f both charts
   vanish; if only its image is nilpotent, the same kernel calculation puts 1
   in J. Zero rings are therefore included. -/
theorem homogeneous_quotient_chart_kernel
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (f : S) (hf : f ∈ 𝒜 1) (K : Ideal S) (hK : K.IsHomogeneous 𝒜) :
    ∃ _ : GradedRing (fun d : ℕ ↦
        (𝒜 d).map (Ideal.Quotient.mk K).toAddMonoidHom),
      ∃ q : Away 𝒜 f →+*
          Away (fun d : ℕ ↦ (𝒜 d).map (Ideal.Quotient.mk K).toAddMonoidHom)
            (Ideal.Quotient.mk K f),
        (∀ (d : ℕ) (s : S) (hs : s ∈ 𝒜 (d • (1 : ℕ))),
          (q (Away.mk 𝒜 hf d s hs)).val =
            Localization.mk (Ideal.Quotient.mk K s)
              (⟨(Ideal.Quotient.mk K f) ^ d, ⟨d, rfl⟩⟩ :
                Submonoid.powers (Ideal.Quotient.mk K f))) ∧
        Function.Surjective q ∧
        ∃ J : Ideal (Away 𝒜 f),
          J = Ideal.span {x | ∃ (d : ℕ) (s : S) (hs : s ∈ 𝒜 (d • (1 : ℕ))),
            s ∈ K ∧ Away.mk 𝒜 hf d s hs = x} ∧
          RingHom.ker q = J ∧
          ∃ e : (Away 𝒜 f ⧸ J) ≃+*
              Away (fun d : ℕ ↦ (𝒜 d).map (Ideal.Quotient.mk K).toAddMonoidHom)
                (Ideal.Quotient.mk K f),
            ∀ x : Away 𝒜 f, e (Ideal.Quotient.mk J x) = q x := by
  sorry

end HomogeneousLocalization
