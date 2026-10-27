/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.AlgebraicGeometry.CurveNormalizationCoherentSupport
import Sheaf.AlgebraicGeometry.CoherentFiniteSupportSkyscrapers
import Sheaf.TraceFormula.CurveNormalizationCompletion
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Local normalization defect and its canonical completion comparison

Source: Stacks Project, `varieties.tex`, Tags 0C1R (lemma-prepare-delta-invariant),
(1)--(9), and 0C3V (lemma-normalization-same-after-completion), specialized to a
reduced curve over an algebraically closed field.
(blueprint: lem-trf-curve-delta-completion-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Local normalization defect and its canonical completion comparison.
Source: Stacks Project, `literature/stacks-project/varieties.tex`, Tags 0C1R and 0C3V
(blueprint: lem-trf-curve-delta-completion-data).

Proof:
1. Apply lem-trf-normalization-affine-stalk-closure to get finite surjective
   normalization, injections on opens and stalks, and the finite integral-closure
   stalk model. Apply lem-trf-curve-normalization-coherent-support at the closed
   point: its local ring is reduced Noetherian of dimension one, essentially finite
   type over k, with structural residue field k.
2. The fibre is nonempty by surjectivity and finite by
   lem-weil-pbc-finite-closed-map-finite-fibres. An integral prime over a maximal
   ideal is maximal (lem-weil-pbc-integral-prime-over-maximal-maximal), so its
   points are closed. Their residue fields are finite extensions of k, hence the
   structural maps are isomorphisms by lem-weil-pbc-alg-closed-finite-extension-trivial.
3. The coherent quotient has finite closed support. Apply
   lem-trf-coherent-finite-support-skyscrapers to obtain a simple filtration of
   its stalk, using the empty filtration when the stalk is zero.
4. Each simple factor is cyclic with kernel the unique maximal ideal, and hence
   is structurally k. Lift bases along the filtration and use
   lem-weil-pbc-length-additive-short-exact: length and k-dimension both equal
   the number of factors, including zero factors.
5. Apply lem-trf-curve-normalization-completion to the local ring: its completion
   is reduced of dimension one, and the completed normalization is its integral
   closure in its total fractions. Use lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring and
   lem-weil-pbc-module-completion-complete for the Noetherian complete local
   structure and the structural residue field identification.
6. Apply lem-trf-finite-colength-completion-comparison. Its map on representatives
   sends b+A to the completed b modulo H, and is A-linear, hence k-linear for
   structural scalars. Its tensor isomorphism sends a tensor b to i(a) times b.
   The finite quotient equations specify i as the canonical completion map.
   The H-compatible integral-closure isomorphism is unique: any two differ by
   an H-automorphism of its integral closure in Q(H), which fixes every fraction.
7. The smooth locus is the normal locus by
   lem-trf-curve-normalization-coherent-support. At a smooth point the quotient
   vanishes, so the structural inclusion is also surjective and identifies B with A.
-/
theorem curve_delta_completion_data
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (hpure : X.IsPureDimension 1)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsFinite X.fromReducedNormalization ∧
    Surjective X.fromReducedNormalization ∧
    Nonempty {y : X.reducedNormalization // X.fromReducedNormalization y = x} ∧
    Set.Finite {y : X.reducedNormalization | X.fromReducedNormalization y = x} ∧
    (∀ U : X.Opens, Function.Injective (X.fromReducedNormalization.app U).hom) ∧
    (∀ y : {y : X.reducedNormalization // X.fromReducedNormalization y = x},
      IsClosed ({y.val} : Set X.reducedNormalization) ∧
      ∃ e : X.reducedNormalization.residueField y.val ≅ CommRingCat.of k,
        Spec.map e.inv = X.reducedNormalization.fromSpecResidueField y.val ≫
          X.fromReducedNormalization ≫ (X ↘ Spec (.of k))) ∧
    _root_.IsReduced (X.presheaf.stalk x) ∧
    IsLocalRing (X.presheaf.stalk x) ∧
    ringKrullDim (X.presheaf.stalk x) = 1 ∧
    ((X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom)).EssFiniteType ∧
    ∃ (hnoeth : IsNoetherianRing (X.presheaf.stalk x))
      (e : X.residueField x ≅ CommRingCat.of k),
      Spec.map e.inv = X.fromSpecResidueField x ≫ (X ↘ Spec (.of k)) ∧
    Function.Injective (algebraMap (X.presheaf.stalk x)
      (normalizationPushforwardStalk X x)) ∧
    Module.Finite (X.presheaf.stalk x) (normalizationPushforwardStalk X x) ∧
    Nonempty (normalizationPushforwardStalk X x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x))) ∧
    (∃ r : ℕ, ∃ F : Fin (r + 1) → Submodule (X.presheaf.stalk x)
        (normalizationPushforwardStalk X x ⧸ (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X x)).range),
      F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧
      (∀ j : Fin r, F j.castSucc < F j.succ) ∧
      (∀ j : Fin r, IsSimpleModule (X.presheaf.stalk x)
        (F j.succ ⧸ Submodule.comap (F j.succ).subtype (F j.castSucc))) ∧
      Module.length (X.presheaf.stalk x)
        (normalizationPushforwardStalk X x ⧸ (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X x)).range) = r) ∧
    @Module.Finite k (normalizationPushforwardStalk X x ⧸
        (Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)).range) _ _
      (Module.compHom _
        ((X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom))) ∧
    @Module.finrank k (normalizationPushforwardStalk X x ⧸
        (Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)).range) _ _
      (Module.compHom _
        ((X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom))) =
      Module.length (X.presheaf.stalk x)
        (normalizationPushforwardStalk X x ⧸ (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X x)).range) ∧
    _root_.IsReduced
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
    IsNoetherianRing
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
    IsLocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
    ringKrullDim
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) = 1 ∧
    Function.Bijective
      ((IsLocalRing.residue (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x))).comp
        ((algebraMap (X.presheaf.stalk x) (AdicCompletion
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          ((X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp
            (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom)))) ∧
    ∃ i : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
        →ₐ[X.presheaf.stalk x]
        AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
          (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
          (normalizationPushforwardStalk X x),
      Function.Injective i ∧
      (∀ (n : ℕ) (a : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) (b : X.presheaf.stalk x),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n a =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ n) b →
        AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
            (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x))) n (i a) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
              (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x))) ^ n)
            (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x) b)) ∧
      (∃ t : (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] normalizationPushforwardStalk X x)
          ≃ₐ[X.presheaf.stalk x]
          AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
            (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
            (normalizationPushforwardStalk X x),
        ∀ (a : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) (b : normalizationPushforwardStalk X x),
          t (a ⊗ₜ[X.presheaf.stalk x] b) = i a *
            algebraMap (normalizationPushforwardStalk X x)
              (AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
                (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
                (normalizationPushforwardStalk X x)) b) ∧
      (∃ ec : AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
            (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
            (normalizationPushforwardStalk X x) ≃+*
          integralClosure
            (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
            (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x))),
        ∀ a : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x),
          ec (i a) = algebraMap _ _ a) ∧
      (∃ eM : (normalizationPushforwardStalk X x ⧸ (Algebra.linearMap (X.presheaf.stalk x)
            (normalizationPushforwardStalk X x)).range) ≃ₗ[X.presheaf.stalk x]
          (AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
              (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
              (normalizationPushforwardStalk X x) ⧸ i.toLinearMap.range),
        ∀ c : normalizationPushforwardStalk X x,
          eM (Submodule.Quotient.mk c) =
            Submodule.Quotient.mk
              (AdicCompletion.of ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
                  (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)))
                (normalizationPushforwardStalk X x) c)) ∧
      ((∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ (X ↘ Spec (.of k)))) →
        Function.Bijective (algebraMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X x)) ∧
        Subsingleton (normalizationPushforwardStalk X x ⧸
          (Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)).range)) := by
  sorry

end AlgebraicGeometry.Scheme
