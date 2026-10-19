/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.RingTheory.CompletedJacobianPresentation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.Functoriality
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Sheaf.RingTheory.FieldExtensionCompletionPresentation
import Sheaf.TraceFormula.CompletedJacobianDifferentials
import Sheaf.TraceFormula.SeparableResidueCoefficientSection

/-!
# Formal presentations at finite separable closed points

Source: Stacks Project, varieties.tex, Tags 0C52, 0C54, 0C4Y, 0C50, and curves.tex,
Tag 0C4D (blueprint: lem-trf-separable-closed-point-formal-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Evaluation at the specified residue-field embedding, sending `s ⊗ c` to `ι(s mod p) * c`.
Source: Stacks Project, Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-closed-point-formal-presentation). -/
def closedPointTensorEvaluation {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    (p : Ideal S) [p.IsPrime] (ι : p.ResidueField →ₐ[k] K) :
    (S ⊗[k] K) →ₐ[k] K :=
  Algebra.TensorProduct.lift
    (ι.comp (IsScalarTower.toAlgHom k S p.ResidueField)) (AlgHom.id k K)
    (fun _ _ ↦ Commute.all _ _)

/-- The localization at the kernel of the canonical point evaluation.
Source: Stacks Project, Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-closed-point-formal-presentation). -/
abbrev ClosedPointBaseChangeLocalRing {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    (p : Ideal S) [p.IsPrime] (ι : p.ResidueField →ₐ[k] K) :=
  @Localization.AtPrime (S ⊗[k] K) _
    (RingHom.ker (closedPointTensorEvaluation p ι).toRingHom)
    (RingHom.ker_isPrime (closedPointTensorEvaluation p ι).toRingHom)

/-- The structural action of `K` on the localized tensor product, through `1 ⊗ c`.
Source: Stacks Project, Tag 0C54
(blueprint: lem-trf-separable-closed-point-formal-presentation). -/
instance closedPointBaseChangeLocalRingAlgebra {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    (p : Ideal S) [p.IsPrime] (ι : p.ResidueField →ₐ[k] K) :
    Algebra K (ClosedPointBaseChangeLocalRing p ι) :=
  ((algebraMap (S ⊗[k] K) (ClosedPointBaseChangeLocalRing p ι)).comp
    Algebra.TensorProduct.includeRight.toRingHom).toAlgebra

/-- Formal structure, canonical completed differentials, and extension of the coefficient field.
`p.ResidueField` is canonically `S/p` because `p` is maximal. The completion residue assertion
uses the canonical projection `evalOneₐ`; the field comparison is an algebra equivalence with
this projection as its reduction. The localized map and its completed map are characterized
on the original ring and on every finite quotient, respectively. Consequently the comparison
of variable images refers to the canonical map of completions.

Source: Stacks Project, varieties.tex, Tags 0C52, 0C54, 0C4Y, 0C50; curves.tex, Tag 0C4D
(blueprint: lem-trf-separable-closed-point-formal-presentation).

Proof:
1. Finite type over a field implies Noetherianity (lem-weil-pbc-finite-type-algebra-noetherian).
   Localization is Noetherian local (lem-weil-pbc-flat-local-ring-maps). Its residue field is
   S/p. Completion is Noetherian (lem-weil-pbc-adic-completion-noetherian), local, with extended
   maximal ideal and the same residue field (lem-weil-pbc-local-completion-local-ring).
   It is complete by lem-weil-pbc-adic-completion-mod-ideal.
2. The finite separable residue field has a k-algebra section
   (lem-trf-separable-residue-coefficient-section). Choose generators of the maximal ideal and
   evaluate power series using lem-weil-pbc-power-series-universal-property-complete.
   The source is Noetherian complete by lem-weil-pbc-power-series-field-cohen-regular-complete.
   Surjectivity modulo the variable ideal implies surjectivity by
   lem-weil-pbc-complete-source-surjective-mod-ideal. Choose finite kernel generators; reduction
   to the residue field shows that the kernel lies in the variable ideal.
3. Add dummy variables and their equations if needed to arrange n at least two.
4. For every presentation apply lem-trf-completed-jacobian-differentials. The continuous
   extension of da sends each variable image to its differential; the Jacobian columns are
   precisely the kernel of the resulting surjection onto the completed differential module.
5. Evaluation S tensor K to K is onto and contracts its kernel to p. Field extension is
   faithfully flat (lem-weil-pbc-field-extension-base-change-faithfully-flat); localization
   gives a flat local map (lem-weil-pbc-flat-local-ring-maps), hence faithfully flat by
   lem-pc-local-flat-faithful-flat-reflects-surjective. Finite type gives Noetherianity.
   The closed fibre is the localization of F tensor K at the evaluation kernel. It is reduced
   by lem-weil-pbc-finite-separable-tensor-field-reduced and finite dimensional, hence a field,
   namely K. Therefore the extended maximal ideal equals the maximal ideal of B.
6. Apply lem-trf-field-extension-completion-presentation to every chosen presentation. The
   finite-quotient inverse limit gives the canonical completion comparison, fixes constants
   through the specified embedding and preserves all variable images (Tag 0C54).
7. Apply lem-trf-completed-jacobian-differentials over K to B, whose residue field is K.
   Coefficient extension commutes with partial derivatives, giving the same Jacobian cokernel.
-/
theorem separable_closed_point_formal_presentation
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k p.ResidueField] [Algebra.IsSeparable k p.ResidueField] :
    IsNoetherianRing (Localization.AtPrime p) ∧
    ∃ (_ : IsNoetherianRing (LocalCompletion (Localization.AtPrime p)))
      (_ : IsLocalRing (LocalCompletion (Localization.AtPrime p))),
      IsLocalRing.maximalIdeal (LocalCompletion (Localization.AtPrime p)) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (LocalCompletion (Localization.AtPrime p))) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (LocalCompletion (Localization.AtPrime p)))
        (LocalCompletion (Localization.AtPrime p)) ∧
      (∃ e : IsLocalRing.ResidueField (LocalCompletion (Localization.AtPrime p)) ≃ₐ[k]
          p.ResidueField,
        ∀ z : LocalCompletion (Localization.AtPrime p),
          e (IsLocalRing.residue _ z) =
            AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) z) ∧
      Nonempty (FormalLocalPresentation k (Localization.AtPrime p)) ∧
      (∀ P : FormalLocalPresentation k (Localization.AtPrime p),
        HasCompletedJacobianPresentation k (Localization.AtPrime p) p.ResidueField
          P.n P.s P.map.toRingHom P.relation ∧
        ∀ (K : Type (max u v w)) [Field K] [Algebra k K] (ι : p.ResidueField →ₐ[k] K),
          IsNoetherianRing (ClosedPointBaseChangeLocalRing p ι) ∧
          ∃ g : Localization.AtPrime p →+* ClosedPointBaseChangeLocalRing p ι,
            (∀ a : S, g (algebraMap S (Localization.AtPrime p) a) =
              algebraMap (S ⊗[k] K) (ClosedPointBaseChangeLocalRing p ι)
                (a ⊗ₜ[k] (1 : K))) ∧
            g.FaithfullyFlat ∧ IsLocalHom g ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map g =
              IsLocalRing.maximalIdeal (ClosedPointBaseChangeLocalRing p ι) ∧
            (∃ e : IsLocalRing.ResidueField (ClosedPointBaseChangeLocalRing p ι) ≃ₐ[K] K,
              ∀ a : S, ∀ c : K,
                e (IsLocalRing.residue _
                  (algebraMap (S ⊗[k] K) (ClosedPointBaseChangeLocalRing p ι)
                    (a ⊗ₜ[k] c))) = ι (algebraMap S p.ResidueField a) * c) ∧
            ∃ (_ : IsNoetherianRing (LocalCompletion (ClosedPointBaseChangeLocalRing p ι)))
              (_ : IsLocalRing (LocalCompletion (ClosedPointBaseChangeLocalRing p ι))),
              IsAdicComplete
                (IsLocalRing.maximalIdeal (LocalCompletion (ClosedPointBaseChangeLocalRing p ι)))
                (LocalCompletion (ClosedPointBaseChangeLocalRing p ι)) ∧
              ∃ h : LocalCompletion (Localization.AtPrime p) →+*
                  LocalCompletion (ClosedPointBaseChangeLocalRing p ι),
                (∀ (r : ℕ) (z : LocalCompletion (Localization.AtPrime p))
                    (a : Localization.AtPrime p),
                  AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) r z =
                      Ideal.Quotient.mk
                        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ r) a →
                    AdicCompletion.evalₐ
                        (IsLocalRing.maximalIdeal (ClosedPointBaseChangeLocalRing p ι)) r (h z) =
                      Ideal.Quotient.mk
                        ((IsLocalRing.maximalIdeal (ClosedPointBaseChangeLocalRing p ι)) ^ r)
                        (g a)) ∧
                ∃ φ : MvPowerSeries (Fin P.n) K →ₐ[K]
                    LocalCompletion (ClosedPointBaseChangeLocalRing p ι),
                  (∀ f : MvPowerSeries (Fin P.n) p.ResidueField,
                    φ (MvPowerSeries.map ι.toRingHom f) = h (P.map f)) ∧
                  (∃ e : (MvPowerSeries (Fin P.n) K ⧸
                      Ideal.span (Set.range (fun j : Fin P.s ↦
                        MvPowerSeries.map ι.toRingHom (P.relation j)))) ≃ₐ[K]
                        LocalCompletion (ClosedPointBaseChangeLocalRing p ι),
                    IsLocalHom e.toRingHom ∧
                    ∀ f : MvPowerSeries (Fin P.n) K, e (Ideal.Quotient.mk _ f) = φ f) ∧
                  HasCompletedJacobianPresentation K (ClosedPointBaseChangeLocalRing p ι) K
                    P.n P.s φ.toRingHom
                    (fun j : Fin P.s ↦ MvPowerSeries.map ι.toRingHom (P.relation j))) := by
  sorry

end Algebra
