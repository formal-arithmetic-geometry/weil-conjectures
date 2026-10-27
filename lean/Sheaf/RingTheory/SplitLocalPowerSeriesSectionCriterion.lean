/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Algebra.Module.Torsion.Basic

import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import Sheaf.RingTheory.CompleteLocalCotangentGradedRigidity
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Power-series presentation detected by finite local sections

Source: Stacks Project, Formal Deformation Theory, Tag 06SG (`lemma-power-series`).
(blueprint: lem-sfb-split-local-power-series-section-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace IsLocalRing

/-- A split complete local inclusion with a kernel cotangent basis has the canonical
power-series presentation, and sections at all sufficiently large finite levels make it
an isomorphism. The natural residue-field scalar action on the basis quotient is transported
along `eC.symm`, so the specified basis is over `l` itself.
The submodule `maximalIdeal C • ⊤` of `ker ρ` is precisely `m_C I`.
The maps `p`, `qS`, and `qC` below are the canonical quotient and residue maps:
their composites with the surjective quotient projections specify them uniquely.
Levels are indexed by `n + 1`, so level zero is the first, nonzero-exponent quotient.
No coefficient-linearity or compatibility between the sections is imposed.

Source: Stacks Project, Formal Deformation Theory, Tag 06SG (`lemma-power-series`),
with the right-inverse equation from its proof made explicit.
(blueprint: lem-sfb-split-local-power-series-section-criterion)

Proof:
1. Noetherianity of a finite-variable power-series ring gives Noetherianity of S.
   Its nonunits are exactly the series whose constant term belongs to m_B, by the
   power-series unit criterion. Its maximal ideal is m_B S + (X), and its residue
   field is l via constant coefficients. Completeness of B gives completeness of S
   for this combined ideal, including the case of zero variables.
2. Locality of ρ puts I inside m_C. Adic power-series evaluation at the x_j gives
   φ. Polynomial truncations converge, so continuity and separation give uniqueness.
   The coefficient and variable images show locality and the marked residue identity.
3. The splitting gives m_C = i(m_B) ⊕ I and
   m_C² = i(m_B²) ⊕ m_C I. The analogous decomposition for S identifies the
   cotangent map with the identity on m_B/m_B² and the specified basis on I/m_C I.
4. Apply the complete local cotangent surjectivity criterion (Tag 06GZ) to φ.
   It is surjective and induces the surjections p_n. The finite power quotients are
   Artinian local, with residue l. For exponent at least two their cotangent spaces
   agree with those of the complete rings, so p_n is a cotangent isomorphism.
5. For each sufficiently large n, p_n σ_n = id makes the cotangent map of σ_n
   inverse to that of p_n. The quotients are complete Noetherian local rings since
   their maximal ideals are nilpotent. Tag 06GZ makes σ_n surjective; its right-inverse
   equation makes it injective. Thus p_n is an isomorphism, independently at each level.
6. The kernel of φ lies in every sufficiently large power of m_S, hence in every
   power. Separation makes it zero. Its inverse preserves maximal-ideal powers and
   is continuous, giving the claimed complete local B-algebra isomorphism. -/
theorem splitLocal_powerSeries_section_criterion
    (B : Type u) (C : Type v) (l : Type w)
    [CommRing B] [CommRing C] [Field l]
    [IsNoetherianRing B] [IsNoetherianRing C] [IsLocalRing B] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal B) B] [IsAdicComplete (maximalIdeal C) C]
    [Algebra B C] [IsLocalHom (algebraMap B C)]
    (eB : ResidueField B ≃+* l) (eC : ResidueField C ≃+* l)
    (ρ : C →+* B) [IsLocalHom ρ]
    (hi : Function.Injective (algebraMap B C))
    (hsplit : ρ.comp (algebraMap B C) = RingHom.id B)
    (hires : eC.toRingHom.comp ((residue C).comp (algebraMap B C)) =
      eB.toRingHom.comp (residue B))
    (hρres : eB.toRingHom.comp ((residue B).comp ρ) =
      eC.toRingHom.comp (residue C))
    (r : ℕ) (x : Fin r → RingHom.ker ρ)
    (b : @Module.Basis (Fin r) l
      ((RingHom.ker ρ) ⧸ (maximalIdeal C • ⊤ : Submodule C (RingHom.ker ρ))) _ _
      (@Module.compHom (C ⧸ maximalIdeal C) l _ _ _ inferInstance _ eC.symm.toRingHom))
    (hb : ∀ j : Fin r, b j = Submodule.Quotient.mk (x j)) :
    IsNoetherianRing (MvPowerSeries (Fin r) B) ∧
    IsLocalRing (MvPowerSeries (Fin r) B) ∧
    maximalIdeal (MvPowerSeries (Fin r) B) =
      (maximalIdeal B).map MvPowerSeries.C ⊔ Ideal.span (Set.range MvPowerSeries.X) ∧
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin r) B))
      (MvPowerSeries (Fin r) B) ∧
    ∃ eS : ResidueField (MvPowerSeries (Fin r) B) ≃+* l,
      eS.toRingHom.comp (residue (MvPowerSeries (Fin r) B)) =
        (eB.toRingHom.comp (residue B)).comp MvPowerSeries.constantCoeff ∧
      ∃ φ : MvPowerSeries (Fin r) B →ₐ[B] C,
        (∀ j : Fin r, φ (MvPowerSeries.X j) = (x j : C)) ∧
        @Continuous _ C (maximalIdeal (MvPowerSeries (Fin r) B)).adicTopology
          (maximalIdeal C).adicTopology φ ∧
        (∀ ψ : MvPowerSeries (Fin r) B →ₐ[B] C,
          (∀ j : Fin r, ψ (MvPowerSeries.X j) = (x j : C)) →
          @Continuous _ C (maximalIdeal (MvPowerSeries (Fin r) B)).adicTopology
            (maximalIdeal C).adicTopology ψ → ψ = φ) ∧
        IsLocalHom φ.toRingHom ∧
        (eC.toRingHom.comp (residue C)).comp φ.toRingHom =
          eS.toRingHom.comp (residue (MvPowerSeries (Fin r) B)) ∧
        ∃ (p : ∀ n : ℕ,
            (MvPowerSeries (Fin r) B ⧸ maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1)) →+*
              (C ⧸ maximalIdeal C ^ (n + 1)))
          (qS : ∀ n : ℕ,
            (MvPowerSeries (Fin r) B ⧸ maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1)) →+* l)
          (qC : ∀ n : ℕ, (C ⧸ maximalIdeal C ^ (n + 1)) →+* l),
          (∀ n : ℕ,
            IsArtinianRing
              (MvPowerSeries (Fin r) B ⧸ maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1)) ∧
            IsLocalRing
              (MvPowerSeries (Fin r) B ⧸ maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1)) ∧
            IsArtinianRing (C ⧸ maximalIdeal C ^ (n + 1)) ∧
            IsLocalRing (C ⧸ maximalIdeal C ^ (n + 1)) ∧
            Function.Surjective (qS n) ∧ Function.Surjective (qC n) ∧
            (qS n).comp
                (Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1))) =
              eS.toRingHom.comp (residue (MvPowerSeries (Fin r) B)) ∧
            (qC n).comp (Ideal.Quotient.mk (maximalIdeal C ^ (n + 1))) =
              eC.toRingHom.comp (residue C) ∧
            (p n).comp
                (Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1))) =
              (Ideal.Quotient.mk (maximalIdeal C ^ (n + 1))).comp φ.toRingHom ∧
            Function.Surjective (p n) ∧ IsLocalHom (p n) ∧
            (qC n).comp (p n) = qS n) ∧
          ((∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ∃ σ : (C ⧸ maximalIdeal C ^ (n + 1)) →+*
                  (MvPowerSeries (Fin r) B ⧸
                    maximalIdeal (MvPowerSeries (Fin r) B) ^ (n + 1)),
                IsLocalHom σ ∧ (qS n).comp σ = qC n ∧
                  (p n).comp σ = RingHom.id (C ⧸ maximalIdeal C ^ (n + 1))) →
            ∃ e : MvPowerSeries (Fin r) B ≃ₐ[B] C,
              e.toAlgHom = φ ∧
              @Continuous C _ (maximalIdeal C).adicTopology
                (maximalIdeal (MvPowerSeries (Fin r) B)).adicTopology e.symm) := by
  sorry

end IsLocalRing
