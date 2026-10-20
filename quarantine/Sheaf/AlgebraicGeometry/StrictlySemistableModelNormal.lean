/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.StrictlySemistableCurve
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.EtaleNormalRing
import Sheaf.RingTheory.ValuationRingNormal
import Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Normality of a strictly semistable model with smooth generic fibre

Source: Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3,
Proposition 4.3.1, end of the first paragraph of the proof, pp. 27–28
(blueprint: lem-trf-strict-semistable-model-normal).

Normality is expressed by the integrally closed domain condition on every stalk;
there is no Noetherian, separatedness or properness assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A strictly semistable curve over a valuation subring of a separably closed field,
with finitely many prime ideals and smooth generic fibre, has integrally closed local
 domains and is reduced. A valuation subring has linearly ordered ideals, so finiteness
of its prime spectrum is exactly the finite-chain hypothesis.

Source: Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3,
Proposition 4.3.1, proof, end of first paragraph, pp. 27–28
(blueprint: lem-trf-strict-semistable-model-normal).

Proof following the seven steps of the node:
1. Around an arbitrary point choose a strict étale chart over an affine base open.
   A nonempty open of the finite chain Spec V is principal, say D(s), so its ring is
   V[1/s] with fraction field K. Valuation-ring normality
   (`lem-weil-pbc-valuation-ring-normal`) and localization normality
   (`lem-weil-pbc-localization-normal-domain`) make this ring a normal domain.
2. In a chart uv=0, suppose the point maps into the node section. The chart is open,
   since it is étale, hence flat and locally finitely presented
   (`lem-weil-pbc-flat-lfp-open`). Its image meets that section in a nonempty open,
   which contains its generic point. Thus some generic-fibre point maps to the node.
3. Étale base change (`lem-weil-pbc-etale-scheme-base-change`) and localized flatness
   (`lem-weil-pbc-flat-local-ring-maps`) give a flat local map from
   H=(K[u,v]/(uv))_(u,v) into the stalk of that point. It is faithfully flat
   (`lem-weil-pbc-flat-local-hom-faithfully-flat`) and hence injective, using
   `lem-weil-pbc-faithfully-flat-universally-injective` with module H. Neither u nor v
   vanishes in H: their annihilators before localization are (v) and (u), contained
   in (u,v). But smoothness is source local (`lem-weil-pbc-smooth-local-on-source`),
   and `lem-weil-pbc-geometric-regularity-smooth-field-criterion` with K/K makes
   the target stalk regular, hence a domain by `lem-sc-regular-local-domain`.
   This contradicts uv=0. Thus at the original point either u or v is invertible.
4. For a nonzero parameter a, the monomial normal form
   c₀ + sum cₙuⁿ + sum dₘvᵐ embeds B=A[u,v]/(uv-a) into Frac(A)[u,u⁻¹]
   by v=a/u: distinct Laurent exponents and a≠0 show injectivity. Therefore B is a
   domain with fraction field Frac(A)(u), and B_u and B_v are Laurent polynomial rings.
5. Those two localizations are normal by polynomial and localization normality
   (`lem-weil-pbc-polynomial-ring-normal-domain`,
   `lem-weil-pbc-localization-normal-domain`). Their intersection is B: for an element
   sum cₙuⁿ of B_u, membership in B_v forces c₋ₘ/aᵐ in A, so each negative term is
   (c₋ₘ/aᵐ)vᵐ. An element integral over B lies in both normal localizations, hence B.
   Its prime localizations are consequently integrally closed domains.
6. The polynomial charts and the Laurent charts of step 3 are likewise normal.
   Shrink to an affine neighbourhood over the appropriate normal chart. Étale ascent
   (`lem-weil-pbc-etale-over-normal-ring-normal`) makes its coordinate ring normal;
   localization at the point gives the original curve's integrally closed local domain.
7. The point was arbitrary, so the curve is normal. A domain has no nonzero nilpotents,
   so every stalk is reduced, which is equivalent to `IsReduced C`
   (`def-pc-reduced-scheme`). -/
theorem normal_and_reduced_of_strictlySemistableCurve
    {K : Type u} [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] {C : Scheme.{u}} (f : C ⟶ Spec (.of V))
    (hC : IsStrictlySemistableCurve f)
    (hgeneric : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap V K))))) :
    (∀ c : C, IsDomain (C.presheaf.stalk c) ∧ IsIntegrallyClosed (C.presheaf.stalk c)) ∧
      IsReduced C := by
  sorry

end AlgebraicGeometry
