/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.LaurentSeries
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationProperties
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.TraceFormula.CurveNormalizationCompletion
import WeilConjectures.RingTheory.FibrePrimesResidueFields
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-! # Completed normalization and branch geometry of a nodal curve

Source: Stacks Project, curves.tex, Tag 0E68, normalization setup; the completed branch
calculation of Tag 0C4A, Case I; varieties.tex, Tags 0C1R and 0C3V; algebra.tex, Tag 0BI0
(blueprint: lem-sfb-nodal-completed-normalization-model).

The uncompleted normalization is never asserted to be a product. The completion map is
specified in every quotient, and each chosen nodal presentation specifies the axis maps
coefficient by coefficient. The tensor comparison is an algebra equivalence for exactly
that completed-base action. Residues are the actual stalk-to-residue maps at the two points.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Evaluation of a normalization pushforward stalk at a point over x, followed by the
chosen identification of that point's residue field. The stalk transport uses only the
specified equality of its image with x.
Source: Stacks Project, varieties.tex, Tag 0C1R(3), and morphisms.tex, Tag 0C3B
(blueprint: lem-sfb-nodal-completed-normalization-model). -/
def nodalNormalizationBranchResidue (k : Type u) [Field k] (C : Scheme.{u}) (x : C)
    (y : {y : C.reducedNormalization // C.fromReducedNormalization y = x})
    (e : C.reducedNormalization.residueField y.val ≅ CommRingCat.of k) :
    normalizationPushforwardStalk C x →+* k :=
  ((((TopCat.Presheaf.pushforward CommRingCat C.fromReducedNormalization.base).obj
      C.reducedNormalization.presheaf).stalkCongr (.of_eq y.property.symm)).hom ≫
    C.reducedNormalization.presheaf.stalkPushforward CommRingCat
      C.fromReducedNormalization.base y.val ≫ C.reducedNormalization.residue y.val ≫ e.hom).hom

/-- All the global and completed local normalization assertions for a proper reduced
pure one-dimensional split nodal curve. The finite connected components are the actual
summands in reducedNormalization. In the local clauses B is the actual pushforward ring
stalk, canonically identified over A with its integral closure in total fractions.
The maps on completions and tensors are characterized on finite quotients and pure tensors.
For every chosen nodal presentation, e composed with i is restriction to the two axes.
The kernels of the two actual point-residue maps enumerate exactly the maximal ideals of B.
Only the total quotient ring of the completed local ring is a product of Laurent fields.

Source: Stacks Project, curves.tex, Tag 0E68 (lemma-nodal-vector-fields), normalization
setup, and Tag 0C4A (lemma-2-branches-delta-1), Case I; varieties.tex, Tags 0C1R and 0C3V;
algebra.tex, Tag 0BI0 (blueprint: lem-sfb-nodal-completed-normalization-model).

Proof (the thirteen DAG steps):
1. Properness gives finite type. The field is Noetherian, so C is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, with finitely many irreducible components by
   lem-weil-pbc-noetherian-finitely-many-components. Use the componentwise normalization.
2. Apply lem-trf-normalization-singular-skyscraper: the nonsmooth locus is finite with
   closed structural k-points; normalization is finite and its stalk is the integral closure.
3. Each reduced component is proper by lem-weil-pbc-proper-fp-permanence. Apply
   lem-sc-normalization-properties and lem-sc-proper-dim-one-projective: its normalization
   is smooth and projective over the perfect field k, and integral, hence connected.
4. The complement of S is smooth, hence normal by lem-sc-smooth-normal. Apply the normal
   open restriction clause of lem-per-componentwise-normalization-properties.
5. The closed point has a component chain of length one and none longer, by
   lem-sc-scheme-stalk-dimension-generalization-chains. Thus its local ring has dimension
   one, is reduced and Noetherian, and is essentially finite type using an affine chart
   and lem-weil-pbc-localization-noetherian.
6. Apply lem-trf-curve-normalization-completion to identify the completed normalization
   with the integral closure of the completed base in its total quotient ring.
7. Modulo uv, every series is c+u f(u)+v g(v). Restriction to the axes is injective,
   and its image is precisely the equal-constant pairs, with inverse f(u)+g(v)-f(0).
8. A pair is regular exactly when both coordinates are nonzero. Multiply a Laurent pair
   by (u^N,v^N) for sufficiently large N to express it as a regular fraction. Use
   lem-weil-pbc-power-series-domain and lem-weil-pbc-laurent-series-field.
9. The idempotent (1,0) is integral and generates P over the equal-constant subring.
   Apply lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-power-series-normal-domain;
   coordinatewise monic equations show that P is exactly the integral closure.
10. Apply lem-weil-pbc-completion-finite-module-tensor. Its pure-tensor formula is
    multiplicative and fixes the completed base, giving the stated algebra equivalence.
11. By lem-weil-pbc-local-completion-local-ring and lem-weil-pbc-finite-algebra-local-radical,
    every maximal ideal of B contains mB. Reduction of the completion gives B/mB=k×k;
    its two projections are the constant-term maps, with two distinct maximal kernels.
12. Use lem-per-componentwise-normalization-affine-charts, localization of integral closure
    (lem-weil-pbc-integral-closure-commutes-localization), and
    lem-weil-pbc-fibre-ring-primes-residue-fields. The two maximal ideals are the two
    normalization points above x, and their quotient maps are the actual point residues.
13. By lem-weil-pbc-finite-closed-map-finite-fibres, inverse images of finite sets are finite.
    Intersect with each actual normalization summand, including the empty S case.
-/
theorem nodal_completed_normalization_model
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsProper (C ↘ Spec (.of k))] [IsReduced C]
    (hC : Nonempty C) (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, x ∉ (C ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
        (C.presheaf.stalk x) ≃+* (MvPowerSeries (Fin 2) k ⧸ Ideal.span {(MvPowerSeries.X 0 :
          MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (S : Set C) (hS : S = {x : C | x ∉ (C ↘ Spec (.of k)).smoothLocus}) :
    IsNoetherian C ∧ S.Finite ∧
    (∀ x : S, IsClosed ({x.val} : Set C) ∧
      ∃ r : C.residueField x.val ≅ CommRingCat.of k,
        Spec.map r.inv = C.fromSpecResidueField x.val ≫ (C ↘ Spec (.of k))) ∧
    IsFinite C.fromReducedNormalization ∧
    Finite (irreducibleComponents C) ∧
    (∀ Z : irreducibleComponents C,
      ConnectedSpace ((C.reducedNormalizationComponent Z).normalization) ∧
      Smooth ((Sigma.ι (fun Z : irreducibleComponents C ↦ (C.reducedNormalizationComponent
        Z).normalization) Z) ≫ C.fromReducedNormalization ≫ (C ↘ Spec (.of k))) ∧
      IsProjective ((Sigma.ι (fun Z : irreducibleComponents C ↦ (C.reducedNormalizationComponent
        Z).normalization) Z) ≫ C.fromReducedNormalization ≫ (C ↘ Spec (.of k)))) ∧
    IsIso (pullback.snd C.fromReducedNormalization (C ↘ Spec (.of k)).smoothLocus.ι) ∧
    (∀ (Z : irreducibleComponents C) (T : Set C), T.Finite →
      (∀ t ∈ T, IsClosed ({t} : Set C) ∧ t ∈ (C ↘ Spec (.of k)).smoothLocus) →
      {z : (C.reducedNormalizationComponent Z).normalization | ((Sigma.ι (fun Z :
        irreducibleComponents C ↦ (C.reducedNormalizationComponent Z).normalization) Z) ≫
        C.fromReducedNormalization) z ∈ S ∪ T}.Finite) ∧
    (∀ x : S,
      Module.Finite (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val) ∧
      Nonempty ((normalizationPushforwardStalk C x.val) ≃ₐ[(C.presheaf.stalk x.val)] integralClosure
        (C.presheaf.stalk x.val) (FractionRing (C.presheaf.stalk x.val))) ∧
      ringKrullDim (C.presheaf.stalk x.val) = (1 : WithBot ℕ∞) ∧
      ∀ α : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) (C.presheaf.stalk
        x.val)) ≃+* (MvPowerSeries (Fin 2) k ⧸ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin
        2) k) * MvPowerSeries.X 1}),
        ∃ (i : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) (C.presheaf.stalk
          x.val)) →ₐ[(C.presheaf.stalk x.val)] (AdicCompletion ((IsLocalRing.maximalIdeal
          (C.presheaf.stalk x.val)).map (algebraMap (C.presheaf.stalk x.val)
          (normalizationPushforwardStalk C x.val))) (normalizationPushforwardStalk C x.val)))
          (e : (AdicCompletion ((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)).map (algebraMap
            (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val)))
            (normalizationPushforwardStalk C x.val)) ≃+* (PowerSeries k × PowerSeries k)),
          (∀ (n : ℕ) (a : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
            (C.presheaf.stalk x.val))) (b : (C.presheaf.stalk x.val)),
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) n a =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) ^ n) b →
            AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)).map
              (algebraMap (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val))) n (i a)
              =
              Ideal.Quotient.mk (((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)).map
                (algebraMap (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val))) ^ n)
                (algebraMap (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val) b)) ∧
          Function.Injective i ∧
          (∀ h : MvPowerSeries (Fin 2) k,
            e (i (α.symm (Ideal.Quotient.mk _ h))) =
              (PowerSeries.mk (fun n ↦ MvPowerSeries.coeff (Finsupp.single 0 n) h),
                PowerSeries.mk (fun n ↦ MvPowerSeries.coeff (Finsupp.single 1 n) h))) ∧
          (∀ p : (PowerSeries k × PowerSeries k), (∃ a : (AdicCompletion (IsLocalRing.maximalIdeal
            (C.presheaf.stalk x.val)) (C.presheaf.stalk x.val)), e (i a) = p) ↔
            PowerSeries.constantCoeff p.1 = PowerSeries.constantCoeff p.2) ∧
          (∃ E : (AdicCompletion ((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)).map
            (algebraMap (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val)))
            (normalizationPushforwardStalk C x.val)) ≃+* integralClosure (AdicCompletion
            (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) (C.presheaf.stalk x.val))
            (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
            (C.presheaf.stalk x.val))),
            ∀ a : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
              (C.presheaf.stalk x.val)), E (i a) = algebraMap (AdicCompletion
              (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)) (C.presheaf.stalk x.val))
              (integralClosure (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
              (C.presheaf.stalk x.val)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal
              (C.presheaf.stalk x.val)) (C.presheaf.stalk x.val)))) a) ∧
          (∃ tensor : @AlgEquiv (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
            (C.presheaf.stalk x.val)) ((AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk
            x.val)) (C.presheaf.stalk x.val)) ⊗[(C.presheaf.stalk x.val)]
            (normalizationPushforwardStalk C x.val)) (PowerSeries k × PowerSeries k)
              inferInstance inferInstance inferInstance inferInstance
                (e.toRingHom.comp i.toRingHom).toAlgebra,
            ∀ (a : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
              (C.presheaf.stalk x.val))) (b : (normalizationPushforwardStalk C x.val)),
              tensor (a ⊗ₜ[(C.presheaf.stalk x.val)] b) =
                e (i a * AdicCompletion.of ((IsLocalRing.maximalIdeal (C.presheaf.stalk x.val)).map
                  (algebraMap (C.presheaf.stalk x.val) (normalizationPushforwardStalk C x.val)))
                  (normalizationPushforwardStalk C x.val) b)) ∧
          (∃ q : (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
            (C.presheaf.stalk x.val))) ≃+* (LaurentSeries k × LaurentSeries k),
            ∀ a : (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
              (C.presheaf.stalk x.val)),
              q (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x.val))
                (C.presheaf.stalk x.val)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal
                (C.presheaf.stalk x.val)) (C.presheaf.stalk x.val))) a) =
                (algebraMap (PowerSeries k) (LaurentSeries k) (e (i a)).1,
                  algebraMap (PowerSeries k) (LaurentSeries k) (e (i a)).2)) ∧
          (∃ (y : Fin 2 ≃ {y : C.reducedNormalization // C.fromReducedNormalization y = x.val})
            (r : ∀ a : Fin 2, C.reducedNormalization.residueField (y a).val ≅ CommRingCat.of k)
            (M : Fin 2 ≃ {J : Ideal (normalizationPushforwardStalk C x.val) // J.IsMaximal})
            (res : ∀ a : Fin 2, ((normalizationPushforwardStalk C x.val) ⧸ (M a).val) ≃+* k),
            (∀ a : Fin 2, Function.Surjective (nodalNormalizationBranchResidue k C x.val
              (y a) (r a)) ∧
              RingHom.ker (nodalNormalizationBranchResidue k C x.val (y a) (r a)) = (M a).val ∧
              ∀ b : (normalizationPushforwardStalk C x.val), res a (Ideal.Quotient.mk (M a).val b) =
                nodalNormalizationBranchResidue k C x.val (y a) (r a) b) ∧
            (∀ b : (normalizationPushforwardStalk C x.val),
              nodalNormalizationBranchResidue k C x.val (y 0) (r 0) b =
                PowerSeries.constantCoeff (e (AdicCompletion.of ((IsLocalRing.maximalIdeal
                  (C.presheaf.stalk x.val)).map (algebraMap (C.presheaf.stalk x.val)
                  (normalizationPushforwardStalk C x.val))) (normalizationPushforwardStalk C x.val)
                  b)).1 ∧
              nodalNormalizationBranchResidue k C x.val (y 1) (r 1) b =
                PowerSeries.constantCoeff (e (AdicCompletion.of ((IsLocalRing.maximalIdeal
                  (C.presheaf.stalk x.val)).map (algebraMap (C.presheaf.stalk x.val)
                  (normalizationPushforwardStalk C x.val))) (normalizationPushforwardStalk C x.val)
                  b)).2))) := by
  sorry

end AlgebraicGeometry.Scheme
