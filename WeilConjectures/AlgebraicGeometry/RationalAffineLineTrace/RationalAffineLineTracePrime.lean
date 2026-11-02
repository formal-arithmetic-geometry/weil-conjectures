/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalAffineLineTrace.RationalAffineLineTraceData

/-! Prime-field part of the rational affine-line trace. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalAffineLineTrace

open CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The prime-field trace identifies the actual compact-support image of the unit
with the recorded negative signed Tate line. Its source is bounded constructible.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-thm-inversion/
lem-fd-first-formula.proof.md, constant-sheaf paragraph, and
sk-lem-wft-character-integral/lem-fd-character-integral.proof.md, coefficients paragraph
(blueprint: lem-fd-rational-affine-line-prime-trace).

Proof, retaining steps 1--6 of the parent argument:
1. Begin over s0 = Spec F_p. Embed E in the fixed algebraic closure, put R = O_E,
   and choose a uniformizer pi with ell = u pi^e. The rings A_n = R/ell^n = R/pi^(en)
   are finite by def-weil-l-adic-coefficient-extension. The Noetherian base s0 has
   ell^n invertible. Apply lem-amb-affine-space-top-trace in dimension one to obtain
   the projective-line-normalized finite trace Ra0! A_n(1)[2] ≅ A_n.
2. Keep this same compactification. The exact open-extension comparison of
   lem-cbc-proetale-extension-zero-comparison identifies the etale and pro-etale
   open extensions termwise. For the proper qcqs projective-line projection,
   prop-weil-pbc-comparison-direct-image identifies their direct images on this
   bounded-below input. Then lem-sf-module-object-ordinary-coefficient-equivalence
   identifies the coefficient, tensor and actual proper/open composite with the
   native finite module-object construction. Thus these are actual native traces.
3. Put L = R_X0(1)[2] and C = Ra0! L. The Tate sheaf is lisse free of rank one.
   Clause (4) of sk-lem-integral-models and sk-thm-sf-ctf-stability put L and C in
   the bounded constructible finite-Tor category. Clause (2) gives derived
   completeness of C and R_s0. The pi-power and ell-power towers are cofinal.
   The actual scalar mates of sk-prop-scalar-six identify the reductions of C
   with Ra0!,A_n A_n(1)[2]. The source Tate comparisons are the quotient maps on
   compatible roots; on a common trivializing cover this is R tensor_R A_n = A_n.
4. Use det-sp-tower-p1-adjunction to construct the whole-system projective-line
   counit, and compose with the system open-extension counit supplied by
   lem-coef-semilinear-derived-sections. Its evaluated maps are the finite traces
   from step 1, since that normalized trace is precisely this composite counit.
   The equation of lem-pur-vector-trace-scalar-descent identifies the quotient
   comparisons with normalized Tate balancing even for non-flat quotients.
   The scalar mates respect coefficient composition and counits, so this is a map
   from the actual reduction tower of C to that of R_s0. Evaluations detect
   isomorphisms by lem-coef-semilinear-derived-sections. Apply the derived inverse
   limit to the resulting system isomorphism. By sk-lem-sp-tower its completion
   unit is invertible on these bounded constructible objects. This gives
   t_R : C ≅ R_s0; no lifting of a merely levelwise collection of maps is used.
5. Apply ordinary derived extension of scalars R → E. This is a listed coefficient
   map of sk-prop-scalar-six, and its compact-support comparison is invertible on
   these finite-Tor objects. The defining scalar extension of the locally free
   integral Tate line gives E tensor_R R(1) = E(1). Thus
   t_E : Ra0!,E E_X0(1)[2] ≅ E_s0 in the native ordinary derived category.
6. The open projection isomorphism lem-sfb-condensed-support-projection-formula,
   followed by det-thm-sf-pf-field-localizing for the proper projection, identifies
   Ra0! E_X0 tensor E_s0(1)[2] with Ra0! E_X0(1)[2]. The open chart is quasi-compact
   with infinity as closed complement, and its extended unit and Tate line are
   bounded constructible, hence in the required localizing domains. Compose with
   t_E and tensor by E_s0(-1)[-2]. The evaluation isomorphism supplied by
   det-def-sp-tate-twist-locally-free and shift cancellation give I0. This uses
   the actual inverse Tate line, without choosing a trivialization of it.
The unit itself is bounded constructible, since its coefficient module is free of
rank one. The same compact-support constructibility argument gives bounded
constructibility of its image. No field-extension family or trivialization of the
Tate line is part of this assertion. -/
theorem exists_prime_field_trace (p : ℕ) [Fact p.Prime] (hℓp : ℓ ≠ p) :
    ∃ I₀ : compactSupport ℓ E (Spec (.of (ULift.{u} (ZMod p)))) ≅
        negative ℓ E (Spec (.of (ULift.{u} (ZMod p)))),
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (Spec (.of (ULift.{u} (ZMod p)))))
        (compactSupport ℓ E (Spec (.of (ULift.{u} (ZMod p))))) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalAffineLineTrace
