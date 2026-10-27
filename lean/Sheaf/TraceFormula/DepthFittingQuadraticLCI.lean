/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.RingTheory.PresentationFittingIdeal
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.TraceFormula.CompletionLocalCompleteIntersection

/-!
# Depth and the first Fitting ideal at a closed point

Source: Stacks Project, curves.tex, Tags 0C4D, 0C4C, 0C49, and 0C4E
(blueprint: lem-trf-depth-fitting-quadratic-lci).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace Algebra

/-- The binary quadratic quotient appearing in the completed nodal local ring.
This abbreviation expands to the actual power-series quotient; it chooses no data.
Source: Stacks Project, curves.tex, Tags 0C49 and 0C4D
(blueprint: lem-trf-depth-fitting-quadratic-lci). -/
abbrev BinaryQuadraticQuotient {F : Type v} [Field F] (a b c : F) :=
  MvPowerSeries (Fin 2) F ⧸
    Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
      MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
      MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} : Set (MvPowerSeries (Fin 2) F))

/-- Depth one and the maximal first Fitting ideal give the normalized quadratic
completion and a principal LCI neighbourhood. For maximal `p`, `p.ResidueField` is
canonically `S/p`, via `Ideal.bijective_algebraMap_quotient_residueField`.
The finite free surjection only displays the presentation used to compute `Fit₁`;
its ideal is independent of this choice. The constant equation makes `e` an
`F`-algebra isomorphism for the action through `σ`. The final residue equation
states explicitly that its inverse induces the identity on `F`. Both directions
are continuous for the extended-maximal-ideal and quotient-variable-ideal topologies.

Source: Stacks Project, curves.tex, Tags 0C4D (5) to (2), 0C4C, 0C49, and 0C4E
(blueprint: lem-trf-depth-fitting-quadratic-lci).

Proof:
1. Apply lem-trf-separable-closed-point-formal-presentation. The local ring A and
   its completion R are Noetherian local, with residue field F. Fix its k-algebra
   residue section and continuous power-series presentation T -> R, with n >= 2
   and finitely generated kernel contained in the variable ideal.
2. Differentials are finite, since differentials of finitely many algebra generators
   span by the Leibniz rule. Apply lem-weil-pbc-kahler-differentials-localization,
   then lem-trf-fitting-ideal-independence-base-change to A and R. The completed
   differential module has first Fitting ideal mR. Its Jacobian presentation from
   step 1 identifies this ideal with the (n-1)-minors of the Jacobian: multilinear
   expansion reduces arbitrary relation rows to the chosen generating rows.
3. Completion is faithfully flat by lem-weil-pbc-local-completion-faithfully-flat
   and is local. Apply lem-weil-pbc-flat-local-depth-formula. The closed fibre F
   has depth zero, since no element of its zero maximal ideal is a nonzerodivisor
   on F. Thus depth R = depth A = 1.
4. Apply lem-trf-formal-jacobian-quadratic-criterion to obtain a nondegenerate
   binary quadratic quotient over the fixed coefficient section. F-linearity and
   locality give the stated residue identity; local ring isomorphisms preserve
   powers of maximal ideals, giving continuity in both directions.
5. The discriminant implies the equation is nonzero. By
   lem-weil-pbc-power-series-domain it is a nonzerodivisor, and the quotient is
   nonzero by evaluation at zero. Hence its singleton is a regular sequence
   (def-weil-pbc-regular-sequence). Apply
   lem-trf-completion-local-complete-intersection with r=2 and c=1 to obtain
   g outside p with S_g a local complete intersection over k.
-/
theorem depth_fitting_quadratic_lci
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k p.ResidueField] [Algebra.IsSeparable k p.ResidueField]
    (hdepth : IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) = 1)
    {n : ℕ} (π : (Fin n → S) →ₗ[S] KaehlerDifferential k S)
    (hπ : Function.Surjective π)
    (hfitting : Ideal.map (algebraMap S (Localization.AtPrime p))
      (π.presentationFittingIdeal 1) = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    (∃ σ : p.ResidueField →ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p),
      (∀ z : p.ResidueField,
        AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (σ z) = z) ∧
      ∃ (a b c : p.ResidueField), b ^ 2 - 4 * a * c ≠ 0 ∧
        ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) ≃+* BinaryQuadraticQuotient a b c,
          (∀ z : p.ResidueField, e (σ z) = algebraMap p.ResidueField _ z) ∧
          @Continuous _ _
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
              (algebraMap (Localization.AtPrime p)
                (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
                  (Localization.AtPrime p)))).adicTopology
            ((Ideal.span (Set.range (fun i : Fin 2 ↦
              (MvPowerSeries.X i : MvPowerSeries (Fin 2) p.ResidueField)))).map
                (Ideal.Quotient.mk _)).adicTopology e ∧
          @Continuous _ _
            ((Ideal.span (Set.range (fun i : Fin 2 ↦
              (MvPowerSeries.X i : MvPowerSeries (Fin 2) p.ResidueField)))).map
                (Ideal.Quotient.mk _)).adicTopology
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
              (algebraMap (Localization.AtPrime p)
                (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
                  (Localization.AtPrime p)))).adicTopology e.symm ∧
          (∀ f : MvPowerSeries (Fin 2) p.ResidueField,
            AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (e.symm (Ideal.Quotient.mk _ f)) = MvPowerSeries.constantCoeff f)) ∧
    ∃ g : S, g ∉ p ∧ IsLocalCompleteIntersection k (Localization.Away g) := by
  sorry

end Algebra
