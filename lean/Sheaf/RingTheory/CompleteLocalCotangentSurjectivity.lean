/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Relative cotangent surjectivity for complete local algebras

Source: Stacks Project, Formal Deformation Theory, Tag 06GZ,
`lemma-surjective-cotangent-space`, equivalence (1) and (3), with coefficient base `C`
and residue field `k` (blueprint: lem-sfb-complete-local-cotangent-surjectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace AlgHom

/-- A continuous local homomorphism between complete Noetherian local `k`-algebras,
compatible with a complete Noetherian local coefficient algebra `C` and the specified
residue-field identifications, is surjective exactly when its relative cotangent map is.

Cotangent surjectivity is expanded on representatives: every `s` in the maximal ideal
of `S` is congruent to `f r`, for some `r` in the maximal ideal of `R`, modulo
`m_C S + m_S²`. This is precisely surjectivity of the induced `k`-linear map
`m_R / (m_C R + m_R²) → m_S / (m_C S + m_S²)`: every source quotient class has such a
representative, and equality of target classes is the ideal-membership condition below.
The maps being local and compatible with `C` ensure that the source denominator maps
into the target denominator. Thus no arbitrary cotangent map is a parameter.

Source: Stacks Project, Formal Deformation Theory, Tag 06GZ,
`lemma-surjective-cotangent-space`, (1) iff (3), with coefficient base `C`
(blueprint: lem-sfb-complete-local-cotangent-surjectivity).

Proof:
1. If `f` is surjective, lift `s ∈ m_S` to `r ∈ R`. Compatibility of the residue
maps implies `r ∈ m_R`. The difference is zero, so the cotangent map is surjective.
2. Conversely, a cotangent lift gives `s - f r ∈ m_C S + m_S²`. Write the first
summand as a finite sum `∑ c_i s_i`, with `c_i` from `m_C`. Replace each `s_i` by its
residue `λ_i ∈ k`: the error lies in `m_S²`, while `∑ c_i λ_i` lifts to `m_R` by
`C`-compatibility and `k`-linearity. Therefore `m_S = f(m_R) + m_S²` additively.
3. Put `J = m_R S`. The preceding equality gives `m_S = J + m_S²`. Noetherianity
makes `m_S/J` finite, and `m_S (m_S/J) = m_S/J`. Since `m_S` is the Jacobson radical,
`lem-weil-pbc-nakayama-jacobson` gives `m_S/J = 0`, hence `J = m_S`.
4. Apply `lem-weil-pbc-complete-source-surjective-mod-ideal` with `I = m_R`.
Completeness gives precompleteness of `R` and, since `I S = m_S`, Hausdorffness
of `S`. The composite `R → S/m_S = k` is surjective by residue compatibility.
The complete-source lemma therefore makes `f` surjective. -/
theorem surjective_iff_relativeCotangent_surjective
    {k : Type u} [Field k]
    {C : Type v} {R : Type w} {S : Type t}
    [CommRing C] [CommRing R] [CommRing S]
    [Algebra k C] [Algebra k R] [Algebra k S]
    [IsLocalRing C] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing C] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (iC : IsLocalRing.ResidueField C ≃ₐ[k] k)
    (iR : IsLocalRing.ResidueField R ≃ₐ[k] k)
    (iS : IsLocalRing.ResidueField S ≃ₐ[k] k)
    (cR : C →ₐ[k] R) (cS : C →ₐ[k] S) (f : R →ₐ[k] S)
    [IsLocalHom cR.toRingHom] [IsLocalHom cS.toRingHom] [IsLocalHom f.toRingHom]
    (hcR : @Continuous C R (IsLocalRing.maximalIdeal C).adicTopology
      (IsLocalRing.maximalIdeal R).adicTopology cR)
    (hcS : @Continuous C S (IsLocalRing.maximalIdeal C).adicTopology
      (IsLocalRing.maximalIdeal S).adicTopology cS)
    (hf : @Continuous R S (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal S).adicTopology f)
    (hresCR : iR.toRingHom.comp (IsLocalRing.ResidueField.map cR.toRingHom) = iC.toRingHom)
    (hresCS : iS.toRingHom.comp (IsLocalRing.ResidueField.map cS.toRingHom) = iC.toRingHom)
    (hresF : iS.toRingHom.comp (IsLocalRing.ResidueField.map f.toRingHom) = iR.toRingHom)
    (hcompat : f.comp cR = cS) :
    Function.Surjective f ↔
      ∀ s : S, s ∈ IsLocalRing.maximalIdeal S →
        ∃ r : R, r ∈ IsLocalRing.maximalIdeal R ∧
          f r - s ∈ (IsLocalRing.maximalIdeal C).map cS.toRingHom ⊔
            IsLocalRing.maximalIdeal S ^ 2 := by
  sorry

end AlgHom
