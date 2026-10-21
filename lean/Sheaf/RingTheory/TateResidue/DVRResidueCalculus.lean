/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.RingTheory.TateResidue.DVRLaurentCoordinates
public import WeilConjectures.RingTheory.TateResidue.LocalResidue
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection

/-! # Tate residue calculus for a discrete valuation subalgebra

Source: Tate, Residues of differentials on curves, §1, pp. 149–151, §2, Theorem 1,
formula (*), R2 and R4, and §3, Theorems 2 and 4
(blueprint: lem-pc-tate-dvr-residue-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace TateResidue

/-- Tate's local residue for a DVR with finite residue extension: fractional principal
parts are finite-dimensional; any linear retraction gives the finite-potent commutator
formula; regular differentials have zero residue; a uniformizer has the residue-field
trace normalization; and every separable coefficient-field coordinate computes the
residue as the trace of the Laurent coefficient of degree `-1`.

The trace used here is the upstream `Module.End.tateTrace`, with finite-potency
`Module.End.IsFinitePotent`. Its stable-subspace characterization, including independence
of the power and subspace, is `Module.End.tateTrace_eq_trace_restrict` (Tate, §1).

Source: Tate, §1, pp. 149–151; §2, Theorem 1, formula (*), R2 and R4;
§3, Theorems 2 and 4 (blueprint: lem-pc-tate-dvr-residue-calculus).

Proof plan, following the node:
1. Use lem-weil-pbc-dvr-unit-times-uniformizer-power. Every nonzero fractional ideal fO
   is t^r O. Its successive quotients are the residue field, so all principal parts
   are finite-dimensional, including f = 0.
2. Apply lem-pc-tate-endomorphism-ideals: multiplication lies in E; π m_f lies in E₁
   and differs from m_f by E₂. Their displayed commutator lies in E₀ and is finite-potent.
   lem-pc-finite-potent-trace-calculus supplies the stable-subspace trace characterization.
3. The zero-trace commutators [E₁,E₂] and [E₀,E] show independence of lifts and π.
   Linearity on E₀ gives bilinearity, and the second argument kills k-constants.
4. For lifts F,G,H, the identity [F,GH]-[FG,H]-[FH,G]=[G,[F,H]] has trace zero.
   Hence the bilinear pairing satisfies Leibniz and descends through the presentation
   of def-weil-pbc-kahler-differentials, giving the upstream localRes.
5. Put B=O+gO and C=B∩f⁻¹O∩(fg)⁻¹O, where inverse images mean multiplication
   inverse images. The commutator maps K into B and kills C. Trace additivity reduces
   its trace to B/C. For f,g in O this is zero; regular differentials are sums of f dg.
6. For f=u/t and g=t, the induced operator on O/tO is multiplication by the residue
   of u. Thus its trace is the residue-field trace, without a separability hypothesis.
7. Apply lem-weil-pbc-adic-completion-mod-ideal and -mod-power. The completion is
   local, t is a nonzerodivisor, and O injects. By lem-weil-pbc-complete-pair-henselian
   it is henselian. For separable residue extension, apply
   new-lem-sc-henselian-separably-generated-residue-section with the empty family.
8. Successive residue lifting gives the power-series coordinate from that section.
   Completeness defines it; cancellation and first nonzero coefficients prove it is
   bijective. Inverting t extends the coordinate to K in the Laurent-series field,
   with K∩O-hat=O.
9. Extend π to K-hat=K+O-hat by π-hat(x+a)=π(x)+a. The intersection equality
   makes it well-defined. Completion identifies B/C with its completed counterpart
   and intertwines the commutators, so their ordinary finite-dimensional traces agree.
10. For the nonnegative-power projection and f=Σ a_i t^i, g=Σ b_j t^j, the diagonal
    at degree r is Σ_(i+j=0) a_i b_j (1_(r≥0)-1_(r+i≥0)). On the finite strip B/C,
    summing in r gives -i=j. Thus the trace is Tr_(κ/k)([t⁻¹] f g').
11. The coefficientwise derivative is a k-derivation. Separability kills differentials
    of κ, and continuity differentiates power series termwise. The displayed generator formula
    specifies the map on all differentials. By linearity,
    steps 9–10 prove the coefficient formula for every ξ and every such coordinate. -/
theorem dvr_residue_calculus (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] (O : Subalgebra k K) [IsDiscreteValuationRing O]
    [IsFractionRing O K] [FiniteDimensional k (IsLocalRing.ResidueField O)] :
    (∀ f : K, FiniteDimensional k
      ((O.toSubmodule.map (act k f)).map O.toSubmodule.mkQ)) ∧
    (∀ π : K →ₗ[k] O, (∀ x : O, π (x : K) = x) → ∀ f g : K,
      Module.End.IsFinitePotent
        ((O.val.toLinearMap.comp π * act k f) * act k g -
          act k g * (O.val.toLinearMap.comp π * act k f)) ∧
      localRes O (f • KaehlerDifferential.D k K g) =
        Module.End.tateTrace
          ((O.val.toLinearMap.comp π * act k f) * act k g -
            act k g * (O.val.toLinearMap.comp π * act k f))) ∧
    (∀ ω : KaehlerDifferential k O,
      localRes O (KaehlerDifferential.map k k O K ω) = 0) ∧
    (∀ t : O, IsLocalRing.maximalIdeal O = Ideal.span {t} → ∀ a : O,
      localRes O (((a : K) * (t : K)⁻¹) • KaehlerDifferential.D k K (t : K)) =
        Algebra.trace k (IsLocalRing.ResidueField O) (IsLocalRing.residue O a)) ∧
    (Algebra.IsSeparable k (IsLocalRing.ResidueField O) →
      ∀ t : O, IsLocalRing.maximalIdeal O = Ideal.span {t} →
        Nonempty (DVRLaurentCoordinates O t) ∧
        ∀ c : DVRLaurentCoordinates O t,
          ∃ d : KaehlerDifferential k K →ₗ[k] LaurentSeries (IsLocalRing.ResidueField O),
            (∀ f g : K, d (f • KaehlerDifferential.D k K g) =
              c.fieldMap f * LaurentSeries.derivative (IsLocalRing.ResidueField O)
                (c.fieldMap g)) ∧
            ∀ ξ : KaehlerDifferential k K,
              localRes O ξ = Algebra.trace k (IsLocalRing.ResidueField O)
                ((d ξ).coeff (-1))) := by
  sorry

end TateResidue
