/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Sheaf.RingTheory.StrictHenselizationFiniteLifts
import Sheaf.RingTheory.HenselianGlobalInertiaComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Strict local fraction fields and normalization inertia

Source: Stacks Project, pione.tex, Tags 0BTD, 0BSW and 0BSM
(blueprint: lem-dl-a1-strict-local-inertia-generic-fibres).

A geometric point `s` specifies the chosen strict henselization at its image `x`.
The map `k` below is the generic structural map, characterized by its composite to `X`.
Pointwise fixing subgroups and normalization inertia use the existing Mathlib definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Strict local fraction fields embed in the separable closure of the function field;
these embeddings are conjugate, their fixing subgroups act trivially on finite étale
geometric generic fibres, and they are conjugate to normalization inertia.
Source: Stacks Project, Tag 0BTD, setup and first proof paragraph; Tag 0BSW,
lemma-identify-inertia; Tag 0BSM, trivial-composition paragraph
(blueprint: lem-dl-a1-strict-local-inertia-generic-fibres).

Proof:
1. lem-sc-integral-scheme-stalks-in-function-field identifies the stalk fraction
   fields with K. On a nonempty affine open, use
   lem-sc-integral-function-field-affine-fraction and
   lem-weil-pbc-affine-open-stalk-localization. Normality of the stalks makes the
   affine ring normal; lem-weil-pbc-normal-ring-integrally-closed-total makes it
   integrally closed in K.
2. Form the integral closure of the stalk in Ω. Choose a prime over its maximal
   ideal by lem-weil-pbc-integral-injective-lying-over; it is maximal by
   lem-weil-pbc-integral-prime-over-maximal-maximal. Obtain an ordinary henselization
   from lem-per-ordinary-henselian-pointed-neighbourhood-limit and
   lem-per-pointed-etale-limit-henselization. The canonical comparison of
   lem-wf-strict-henselization-finite-lifts gives its compatible map to the prescribed
   strict henselization. Apply lem-dl-a1-henselian-global-inertia-comparison to get
   its domain property and its embedding into the localized integral closure in Ω.
   Extend to fractions; compatibility with the stalk inclusion gives k.
3. Given embeddings i,j, extend j composed with the inverse of i on its image by
   lem-exc-etale-embedding-extension-sepclosed. Normality of Ω/K follows from
   lem-weil-pbc-separable-closure-exists-galois; the resulting endomorphism is
   bijective by lem-exc-etale-algebraic-endomorphism-bijective. This works for
   infinite intermediate fields too.
4. If j = g composed with i, h fixes j's image exactly when g⁻¹ h g fixes i's
   image, giving the displayed conjugacy of pointwise fixing subgroups.
5. Base change a finite étale cover by lem-weil-pbc-finite-morphism-permanence and
   lem-weil-pbc-etale-base-change-finite-limits. Its affine algebra is finite étale
   over the strictly henselian local ring of
   lem-weil-pbc-strict-henselization-local-structure.
6. Reduce to the separably closed residue field by
   lem-weil-pbc-henselian-finite-etale-equivalence. By
   lem-weil-pbc-etale-algebra-over-field-product and
   lem-pc-sepclosed-finite-sep-trivial the residue algebra is k^n, including n = 0.
   Full faithfulness lifts this isomorphism and its inverse, giving the splitting.
7. Base change the splitting to the fraction field by
   lem-sc-etale-fibre-product-base-change-coproduct. Every geometric generic point
   is the scalar extension of one of these sections; precomposition by an
   automorphism fixing i leaves it unchanged. The empty cover gives an empty fibre.
8. For an affine normalization prime over x, use
   lem-weil-pbc-integral-closure-commutes-localization to identify the local integral
   closure with the localization of the affine one. Its prime becomes maximal by
   lem-weil-pbc-integral-prime-over-maximal-maximal, with residue field Frac(C/r).
9. Localization preserves the prime stabilizer and its residue action: both send
   c/s modulo r to g(c)/s. Hence affine inertia equals local inertia, including at
   nonclosed points.
10. Apply lem-dl-a1-henselian-global-inertia-comparison at this prime. It identifies
    inertia with the fixing subgroup for one compatible embedding. Steps 3 and 4
    give conjugacy for every compatible embedding. No step assumes Noetherianity.
-/
theorem strictLocalInertiaGenericFibres
    (X : Scheme.{u}) [IsIntegral X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (s : Spec (.of Ξ) ⟶ X) :
    ∃ (_ : IsDomain (strictHenselizationRing s))
      (k : X.functionField →+* FractionRing (strictHenselizationRing s)),
      (Spec.map (CommRingCat.ofHom k) ≫ X.fromSpecFunctionField =
        Spec.map (CommRingCat.ofHom
          (algebraMap (strictHenselizationRing s) (FractionRing (strictHenselizationRing s)))) ≫
          strictHenselizationStructuralMap s) ∧
      (∃ i : FractionRing (strictHenselizationRing s) →+* Ω,
        i.comp k = algebraMap X.functionField Ω) ∧
      (∀ (i j : FractionRing (strictHenselizationRing s) →+* Ω),
        i.comp k = algebraMap X.functionField Ω →
        j.comp k = algebraMap X.functionField Ω →
        ∃ g : Ω ≃ₐ[X.functionField] Ω,
          (∀ z : FractionRing (strictHenselizationRing s), j z = g (i z)) ∧
          ∀ h : Ω ≃ₐ[X.functionField] Ω,
            h ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range j) ↔
              g⁻¹ * h * g ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range i)) ∧
      (∀ P : X.FiniteEtale, ∃ n : ℕ,
        Nonempty (Over.mk (pullback.snd P.obj.hom (strictHenselizationStructuralMap s)) ≅
          Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 (strictHenselizationScheme s))))) ∧
      (∀ (i : FractionRing (strictHenselizationRing s) →+* Ω),
        i.comp k = algebraMap X.functionField Ω →
        ∀ (P : X.FiniteEtale) (g : Ω ≃ₐ[X.functionField] Ω),
          g ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range i) →
          ∀ t : Spec (.of Ω) ⟶ P.obj.left,
            t ≫ P.obj.hom =
              Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
                X.fromSpecFunctionField →
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ t = t) ∧
      (∀ (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U),
        IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧
        IsFractionRing Γ(X, U) X.functionField ∧
        ∀ [Algebra Γ(X, U) Ω] [IsScalarTower Γ(X, U) X.functionField Ω]
          (r : PrimeSpectrum (integralClosure Γ(X, U) Ω)),
          (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, U) (integralClosure Γ(X, U) Ω))) ≫ hU.fromSpec) r =
              s (default : Spec (.of Ξ)) →
          ∀ (i : FractionRing (strictHenselizationRing s) →+* Ω),
            i.comp k = algebraMap X.functionField Ω →
            ∃ g : Ω ≃ₐ[X.functionField] Ω,
              ∀ h : Ω ≃ₐ[X.functionField] Ω,
                h ∈ r.asIdeal.inertia (Ω ≃ₐ[X.functionField] Ω) ↔
                  g⁻¹ * h * g ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range i)) := by
  sorry

end AlgebraicGeometry.Scheme
