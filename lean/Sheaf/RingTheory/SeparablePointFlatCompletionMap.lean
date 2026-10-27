/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.EtaleHenselianRingLift
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatCompletion

/-!
# Completion at a finite separable point after field extension

Source: Stacks Project, Varieties, Tags 0C4Y, 0C4Z, 0C50 and 0C54;
More on Algebra, Tag 0C4G (blueprint: lem-trf-separable-point-flat-completion-map).
The auxiliary declarations name the specific rings and evaluation in this statement.
-/

@[expose] public section

universe u v w

set_option autoImplicit false

open scoped TensorProduct

namespace SeparablePoint

variable {k : Type u} {S : Type v} {K : Type w}
variable [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
variable (p : Ideal S) [p.IsMaximal]

/-- The source local ring in Stacks 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
abbrev Source := Localization.AtPrime p

/-- Evaluation at the selected residue embedding, Stacks 0C50 and 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
def evaluation (iota : (S ⧸ p) →ₐ[k] K) : S ⊗[k] K →ₐ[k] K :=
  Algebra.TensorProduct.lift (iota.comp (Ideal.Quotient.mkₐ k p))
    (AlgHom.id k K) (fun _ _ => Commute.all _ _)

/-- The prime selected by evaluation, Stacks 0C50 and 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
def point (iota : (S ⧸ p) →ₐ[k] K) : PrimeSpectrum (S ⊗[k] K) :=
  ⟨RingHom.ker (evaluation p iota).toRingHom, RingHom.ker_isPrime _⟩

/-- The target local ring in Stacks 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
abbrev Target (iota : (S ⧸ p) →ₐ[k] K) := Localization.AtPrime (point p iota).asIdeal

/-- The source completion in Stacks 0C54, using the actual inverse limit.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
abbrev SourceCompletion := AdicCompletion (IsLocalRing.maximalIdeal (Source p)) (Source p)

/-- The target completion in Stacks 0C54, using the actual inverse limit.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
abbrev TargetCompletion (iota : (S ⧸ p) →ₐ[k] K) :=
  AdicCompletion (IsLocalRing.maximalIdeal (Target p iota)) (Target p iota)

/-- The extended maximal ideal of the source completion, Stacks 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
noncomputable abbrev sourceCompletedIdeal := (IsLocalRing.maximalIdeal (Source p)).map
  (algebraMap (Source p) (SourceCompletion p))

/-- The extended maximal ideal of the target completion, Stacks 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
noncomputable abbrev targetCompletedIdeal (iota : (S ⧸ p) →ₐ[k] K) :=
  (IsLocalRing.maximalIdeal (Target p iota)).map
    (algebraMap (Target p iota) (TargetCompletion p iota))

/-- The structural K-map into the target completion, Stacks 0C54.
(blueprint: lem-trf-separable-point-flat-completion-map). -/
noncomputable def coefficientMap (iota : (S ⧸ p) →ₐ[k] K) :
    K →ₐ[k] TargetCompletion p iota :=
  (IsScalarTower.toAlgHom k (Target p iota) (TargetCompletion p iota)).comp
    ((IsScalarTower.toAlgHom k (S ⊗[k] K) (Target p iota)).comp
      Algebra.TensorProduct.includeRight)

/-- Flatness and coefficient compatibility at a finite separable closed point.
Source: Stacks Project, Varieties, Tags 0C4Y, 0C4Z, 0C50 and 0C54;
More on Algebra, Tag 0C4G (blueprint: lem-trf-separable-point-flat-completion-map).

Proof:
1. `lem-trf-separable-evaluation-local-base-change` gives the maximal evaluation kernel,
   Noetherian local rings and the canonical faithfully flat local fraction map. Flatness
   follows from `def-weil-pbc-faithfully-flat-ring-map`. The usual residue fraction formula
   identifies the source residue with S/p and the target residue with K.
2. `lem-weil-pbc-flat-height-formula` applied at the maximal ideals gives equality of
   dimensions, since the closed fibre is K and a field has dimension zero.
3. `lem-weil-pbc-adic-completion-noetherian` and
   `lem-weil-pbc-local-completion-local-ring` give Noetherianity, locality, the extended
   maximal ideals and the residue identifications. `lem-weil-pbc-module-completion-complete`
   applied to the rings gives completeness for those extended ideals.
4. Apply g componentwise to compatible residue sequences. The maps modulo each power
   commute with reduction and hence define h. First projection identifies its residue
   with iota. This proves locality; the structural K-map has residue the identity.
5. `lem-weil-pbc-flat-completion` gives flatness of this same quotientwise map.
   Extending mB=n again to C gives m_R C=m_C. Preservation of all ideal powers gives
   continuity for the maximal-ideal adic topologies.
6. `lem-weil-pbc-complete-pair-henselian` makes C henselian.
   `lem-weil-pbc-finite-separable-extension-etale` and
   `lem-weil-pbc-etale-ring-map-iff-etale-affine` make F etale over k. For each residue
   section sigma, h sigma and tau iota have the same residue iota. Uniqueness in
   `lem-sc-etale-henselian-ring-lift` makes these k-algebra maps equal.
-/
theorem flat_completion_map
    (hfiniteType : (algebraMap k S).FiniteType)
    [Module.Finite k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)]
    (iota : (S ⧸ p) →ₐ[k] K) :
    (point p iota).asIdeal.IsMaximal ∧
    IsNoetherianRing (Source p) ∧ IsNoetherianRing (Target p iota) ∧
    p.map (algebraMap S (Source p)) = IsLocalRing.maximalIdeal (Source p) ∧
    (point p iota).asIdeal.map (algebraMap (S ⊗[k] K) (Target p iota)) =
      IsLocalRing.maximalIdeal (Target p iota) ∧
    ringKrullDim (Source p) = ringKrullDim (Target p iota) ∧
    IsNoetherianRing (SourceCompletion p) ∧ IsNoetherianRing (TargetCompletion p iota) ∧
    IsLocalRing (SourceCompletion p) ∧ IsLocalRing (TargetCompletion p iota) ∧
    (sourceCompletedIdeal p).IsMaximal ∧ (targetCompletedIdeal p iota).IsMaximal ∧
    IsAdicComplete (sourceCompletedIdeal p) (SourceCompletion p) ∧
    IsAdicComplete (targetCompletedIdeal p iota) (TargetCompletion p iota) ∧
    ∃ (g : Source p →ₐ[k] Target p iota)
      (piA : Source p →ₐ[k] S ⧸ p) (piB : Target p iota →ₐ[k] K)
      (h : SourceCompletion p →ₐ[k] TargetCompletion p iota)
      (piR : SourceCompletion p →ₐ[k] S ⧸ p)
      (piC : TargetCompletion p iota →ₐ[k] K),
      g.toRingHom.Flat ∧ IsLocalHom g ∧
      (∀ (s : S) (d : p.primeCompl),
        g (IsLocalization.mk' (Source p) s d) *
            algebraMap (S ⊗[k] K) (Target p iota) ((d : S) ⊗ₜ[k] (1 : K)) =
          algebraMap (S ⊗[k] K) (Target p iota) (s ⊗ₜ[k] (1 : K))) ∧
      (IsLocalRing.maximalIdeal (Source p)).map g.toRingHom =
        IsLocalRing.maximalIdeal (Target p iota) ∧
      Function.Surjective piA ∧ RingHom.ker piA.toRingHom =
        IsLocalRing.maximalIdeal (Source p) ∧
      (∀ s : S, piA (algebraMap S (Source p) s) = Ideal.Quotient.mk p s) ∧
      Function.Surjective piB ∧ RingHom.ker piB.toRingHom =
        IsLocalRing.maximalIdeal (Target p iota) ∧
      (∀ z : S ⊗[k] K, piB (algebraMap (S ⊗[k] K) (Target p iota) z) =
        evaluation p iota z) ∧
      h.toRingHom.Flat ∧ IsLocalHom h ∧
      @Continuous (SourceCompletion p) (TargetCompletion p iota)
        (sourceCompletedIdeal p).adicTopology (targetCompletedIdeal p iota).adicTopology h ∧
      (∀ (r : ℕ) (x : SourceCompletion p) (a : Source p),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Source p)) r x =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Source p) ^ r) a →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Target p iota)) r (h x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Target p iota) ^ r) (g a)) ∧
      (sourceCompletedIdeal p).map h.toRingHom = targetCompletedIdeal p iota ∧
      Function.Surjective piR ∧ RingHom.ker piR.toRingHom = sourceCompletedIdeal p ∧
      Function.Surjective piC ∧ RingHom.ker piC.toRingHom = targetCompletedIdeal p iota ∧
      (∀ (x : SourceCompletion p) (a : Source p),
        AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Source p)) x =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Source p)) a → piR x = piA a) ∧
      (∀ (x : TargetCompletion p iota) (b : Target p iota),
        AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Target p iota)) x =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Target p iota)) b → piC x = piB b) ∧
      piC.comp h = iota.comp piR ∧
      piC.comp (coefficientMap p iota) = AlgHom.id k K ∧
      (∀ sigma : (S ⧸ p) →ₐ[k] SourceCompletion p,
        piR.comp sigma = AlgHom.id k (S ⧸ p) →
          h.comp sigma = (coefficientMap p iota).comp iota) := by
  sorry

end SeparablePoint
