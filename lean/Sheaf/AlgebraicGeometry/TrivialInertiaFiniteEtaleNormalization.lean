/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields

/-!
# Trivial inertia makes a finite Galois normalization finite etale

Source: Stacks Project, Tags 0BTD and 0BST, `pione.tex`, final normalization argument
of `lemma-normal-pione-quotient-inertia` and `lemma-inertia-invariants-etale`.
(blueprint: lem-dl-a1-trivial-inertia-finite-etale-normalization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A finite Galois normalization of an integral normal scheme with trivial inertia
is finite etale, with its canonical generic fibre and equivariant evaluation description.
No Noetherian, excellence, or prior finiteness assumption is made.

The algebra structures on affine sections are quantified with their scalar-tower
compatibility: this uniquely specifies the composite of the germ map into `X.functionField`
and its inclusion into `L`. The inertia condition uses the equivalent difference criterion:
every integral element has its Galois conjugate congruent to itself modulo the prime.
The fixed-ring equality is expressed elementwise inside `L`.

The geometric action is a homomorphism into permutations, characterized on the unique
algebraic-closure-valued lift of each point. The evaluation equivalence is characterized
by the morphism obtained from the embedding `L → Ω → Ωa`. Its stabilizer at the inclusion
is expressed as the subgroup of automorphisms fixing every element of `L`.

Source: Stacks Project, Tags 0BTD and 0BST, `pione.tex`; the geometric action convention
is Tag 03QR, `lemma-sheaves-point`.
(blueprint: lem-dl-a1-trivial-inertia-finite-etale-normalization)

Proof plan:
1. The affine function-field fraction lemma and the canonical affine local-ring
   identification show that sections on a nonempty affine open are a normal domain;
   normal-ring-integrally-closed-total makes them integrally closed in the function field.
2. Finite Galois fixed-field theory gives `L^Γ = K`. Conjugating monic equations preserves
   the integral closure. An invariant integral element lies in `K`, hence in `A`;
   conversely every element of `A` is fixed. The closure is integral over `A`.
3. Apply finite-group-inertia-invariants-etale at every prime, with trivial inertia.
   The neighborhoods cover, hence the affine morphism is etale. Local finite presentation
   gives finite presentation on affine opens. Integral plus finite presentation gives a
   finite module, hence the affine morphism is finite.
4. Inverse images of opens under `Spec L → X` are empty or the one-point spectrum.
   The same observation for the diagonal proves quasi-separatedness. Relative normalization
   has the stated integral-closure charts, so their finite etale morphisms glue.
5. On a chart the generic fibre ring is `B ⊗[A] K = S⁻¹B = L`. Clear a common denominator
   in a monic equation over `K`: for each `l ∈ L`, some nonzero `d ∈ A` has `d*l ∈ B`.
   These inclusions give the canonical generic-fibre isomorphism independently of the chart.
6. The separable-first/purely-inseparable theorem and triviality of separable extensions
   of a separably closed field make `Ωa/Ω` purely inseparable. Algebraic-closure uniqueness
   extends each automorphism of `Ω`; pure inseparability makes the extension unique.
7. The affine fibre-product and separable-tensor-algebraic-closure theorems identify the
   geometric fibre with the spectrum of a product of copies of `Ωa`. The spectrum of a
   finite product of fields gives exactly one `Ωa`-valued lift of each point. Evaluation
   is the kernel of `a ⊗ c ↦ φ(a)*c`.
8. Normality of `L/K` makes every embedding `L → Ωa` land in `L ⊆ Ω`: its values are
   roots of minimal polynomials splitting in `L`. Thus evaluation has target `Hom_K(L, Ω)`.
9. Contravariance of `Spec` sends precomposition with `Spec τ` to postcomposition with
   `σ` on embeddings. Uniqueness of extensions gives the action law. The inclusion is
   fixed precisely when `σ` fixes every element of `L`, giving `Aut_L(Ω)`.
-/
theorem finiteEtale_normalizationIn_of_trivial_inertia
    (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L]
    (hinertia : ∀ (V : X.Opens) [Nonempty V], IsAffineOpen V →
      ∀ [Algebra Γ(X, V) L] [IsScalarTower Γ(X, V) X.functionField L]
        (q : PrimeSpectrum (integralClosure Γ(X, V) L))
        (g : L ≃ₐ[X.functionField] L),
        (∀ b : integralClosure Γ(X, V) L, ∃ c : integralClosure Γ(X, V) L,
          (c : L) = g (b : L) ∧ c - b ∈ q.asIdeal) → g = 1) :
    (∀ (V : X.Opens) [Nonempty V], IsAffineOpen V →
      ∀ [Algebra Γ(X, V) L] [IsScalarTower Γ(X, V) X.functionField L],
        (∀ b : integralClosure Γ(X, V) L,
          (∀ g : L ≃ₐ[X.functionField] L, g (b : L) = (b : L)) ↔
            ∃ a : Γ(X, V), algebraMap Γ(X, V) L a = (b : L)) ∧
        IsFinite (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, V) (integralClosure Γ(X, V) L)))) ∧
        Etale (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, V) (integralClosure Γ(X, V) L))))) ∧
    QuasiCompact (X.fromSpecOfAlgebraFunctionField L) ∧
    QuasiSeparated (X.fromSpecOfAlgebraFunctionField L) ∧
    IsFinite (X.fromNormalizationIn L) ∧ Etale (X.fromNormalizationIn L) ∧
    (∀ (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
      [Algebra Γ(X, V) L] [IsScalarTower Γ(X, V) X.functionField L],
      ∃ e : (X.fromNormalizationIn L ⁻¹ᵁ V).toScheme ≅
        Spec (.of (integralClosure Γ(X, V) L)),
        e.inv ≫ (X.fromNormalizationIn L ⁻¹ᵁ V).ι ≫ X.fromNormalizationIn L =
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, V) (integralClosure Γ(X, V) L))) ≫ hV.fromSpec) ∧
    (∃ e : Spec (.of L) ≅ pullback (X.fromNormalizationIn L) X.fromSpecFunctionField,
      e.hom ≫ pullback.fst _ _ = (X.fromSpecOfAlgebraFunctionField L).toNormalization ∧
      e.hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))) ∧
    (∀ (Ω Ωa : Type u) [Field Ω] [Field Ωa]
      [Algebra X.functionField Ω] [Algebra L Ω] [IsScalarTower X.functionField L Ω]
      [IsSepClosure X.functionField Ω] [Algebra Ω Ωa] [IsAlgClosure Ω Ωa]
      [Algebra X.functionField Ωa] [IsScalarTower X.functionField Ω Ωa],
      ∃ (E : ↥(pullback (X.fromNormalizationIn L)
          (X.fromSpecOfAlgebraFunctionField Ωa) : Scheme.{u}) ≃ (L →ₐ[X.functionField] Ω))
        (ρ : (Ω ≃ₐ[X.functionField] Ω) →*
          Equiv.Perm ↥(pullback (X.fromNormalizationIn L)
            (X.fromSpecOfAlgebraFunctionField Ωa) : Scheme.{u})),
        (∀ φ : L →ₐ[X.functionField] Ω,
          ∃ z : Spec (.of Ωa) ⟶ pullback (X.fromNormalizationIn L)
              (X.fromSpecOfAlgebraFunctionField Ωa),
            z ≫ pullback.snd _ _ = 𝟙 _ ∧
            z ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom ((algebraMap Ω Ωa).comp φ.toRingHom)) ≫
                (X.fromSpecOfAlgebraFunctionField L).toNormalization ∧
            E (z (IsLocalRing.closedPoint Ωa)) = φ) ∧
        (∀ y : ↥(pullback (X.fromNormalizationIn L)
            (X.fromSpecOfAlgebraFunctionField Ωa) : Scheme.{u}),
          ∃! z : Spec (.of Ωa) ⟶ pullback (X.fromNormalizationIn L)
              (X.fromSpecOfAlgebraFunctionField Ωa),
            z ≫ pullback.snd _ _ = 𝟙 _ ∧ z (IsLocalRing.closedPoint Ωa) = y) ∧
        (∀ σ : Ω ≃ₐ[X.functionField] Ω, ∃! τ : Ωa ≃ₐ[X.functionField] Ωa,
          ∀ a : Ω, τ (algebraMap Ω Ωa a) = algebraMap Ω Ωa (σ a)) ∧
        (∀ (σ : Ω ≃ₐ[X.functionField] Ω) (τ : Ωa ≃ₐ[X.functionField] Ωa),
          (∀ a : Ω, τ (algebraMap Ω Ωa a) = algebraMap Ω Ωa (σ a)) →
          ∀ z : Spec (.of Ωa) ⟶ pullback (X.fromNormalizationIn L)
              (X.fromSpecOfAlgebraFunctionField Ωa),
            z ≫ pullback.snd _ _ = 𝟙 _ →
            ∃ z' : Spec (.of Ωa) ⟶ pullback (X.fromNormalizationIn L)
                (X.fromSpecOfAlgebraFunctionField Ωa),
              z' ≫ pullback.snd _ _ = 𝟙 _ ∧
              z' ≫ pullback.fst _ _ =
                Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ z ≫ pullback.fst _ _ ∧
              ρ σ (z (IsLocalRing.closedPoint Ωa)) = z' (IsLocalRing.closedPoint Ωa)) ∧
        (∀ (σ : Ω ≃ₐ[X.functionField] Ω)
          (y : ↥(pullback (X.fromNormalizationIn L)
            (X.fromSpecOfAlgebraFunctionField Ωa) : Scheme.{u})),
          E (ρ σ y) = σ.toAlgHom.comp (E y)) ∧
        (∀ σ : Ω ≃ₐ[X.functionField] Ω,
          ρ σ (E.symm (IsScalarTower.toAlgHom X.functionField L Ω)) =
              E.symm (IsScalarTower.toAlgHom X.functionField L Ω) ↔
            ∀ a : L, σ (algebraMap L Ω a) = algebraMap L Ω a)) := by
  sorry

end AlgebraicGeometry
