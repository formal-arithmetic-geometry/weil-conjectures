/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.RingTheory.FlatLocalizedModuleBaseChange
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre

/-!
# Absolute normalization of a trait and local sections

Source: Stacks Project, Tags 05GU, 0DCQ and 0DCS, with the explicit normalization,
henselian finite-factor and denominator-spreading argument in the DAG proof.
(blueprint: lem-sfb-trait-absolute-normalization-local-sections)

## Main declarations

* `traitAbsoluteNormalizationMap`: the canonical map from the spectrum of the integral closure.
* `trait_absolute_normalization_local_sections`: its geometry and prescribed-point local sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The map `Spec (integralClosure R Ω) ⟶ Spec R` induced by the structural ring map.

Source: Stacks Project, Algebra, normalization and Spec functoriality; the map `T ⟶ S`
in (blueprint: lem-sfb-trait-absolute-normalization-local-sections).
This is the actual structural map of the integral-closure subalgebra.
-/
noncomputable def traitAbsoluteNormalizationMap (R Ω : Type u) [CommRing R] [CommRing Ω]
    [Algebra R Ω] :
    Spec (CommRingCat.of (integralClosure R Ω)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω)))

/-- Absolute normalization of a trait is fpqc, has the specified generic open and closed
residue fields, and gives local sections through every prescribed closed-fibre rational point.

Source: Stacks Project, Tags 05GU, 0DCQ, 0DCS, 04GH and 0AB1, assembled as in the
proof of (blueprint: lem-sfb-trait-absolute-normalization-local-sections).

Proof:
1. The integral closure `B` is a normal domain integral over `R`, with fraction field `Ω`
   by lem-weil-pbc-integral-closure-algebraic-extension-normal. It is torsion-free over
   the PID `R`, hence flat by lem-weil-pbc-pid-torsion-free-module-flat. The affine
   flatness dictionary gives flatness of `T ⟶ S`. Lying over gives surjectivity;
   an integral affine map is quasi-compact, hence this singleton is an fpqc cover.
2. A nonzero element of `R` is a unit times a power of `π` by
   lem-weil-pbc-dvr-unit-times-uniformizer-power, so `R[1/π] = K`. Scale each algebraic
   element's monic equation by a sufficiently large power of `π` to see `B[1/π] = Ω`.
   The principal-localization open immersion identifies this with `D(π)`, exactly the
   generic inverse image. All other primes contract to the maximal ideal and are
   maximal by lem-weil-pbc-integral-prime-over-maximal-maximal.
3. Roots of lifted monic polynomials lie in `B` by integral closedness, and their
   reductions show every closed residue field is algebraically closed (0DCQ).
   Localizations `A = B_m` are normal and strictly henselian by
   lem-weil-pbc-localization-normal-domain and lem-weil-pbc-gabber-quotient-localizations.
4. Choose one affine neighbourhood `U = Spec C` of the image `x` of the given point.
   By lem-weil-pbc-lft-affine-pairs and lem-weil-pbc-flat-morphism-affine-criterion,
   `C` is finite type and flat over `R`. It is finitely presented by
   lem-weil-pbc-finite-type-noetherian-finite-presentation. The map `h : C ⟶ κ(t)`
   has finite residue extension over `R/(π)`, using
   lem-a1-integral-residue-extension-algebraic and finite generation. Thus `x` is
   closed in the fibre by lem-trf-finite-residue-point-closed-in-fibre.
5. Flat going down (lem-sc-flat-going-down) gives a generic generalization of `x`.
   Apply lem-sfb-quasi-section-nearby-open over the original Noetherian trait to
   obtain an integral dominant closed quasi-section through `x`.
6. Choose an affine neighbourhood `Spec D` of `x` in that quasi-section where the
   map is quasi-finite at `x` (pqf-def-quasifinite). Dominance makes `R ⟶ D`
   injective; the domain `D` is torsion-free, hence flat over the PID `R`. The
   prescribed residue map factors through `D` because its kernel contains the
   quasi-section ideal and its image point belongs to this neighbourhood.
7. Form `P = A ⊗[R] D` and the surjection to `κ(t)` induced by the prescribed map.
   At its kernel, lem-trf-quasi-finite-henselian-tensor-factor identifies the
   localization `E` as a nonzero finite local `A`-algebra with residue `κ(t)`.
8. By lem-weil-pbc-flat-localized-module-base-change, `E` is flat over `A`, and
   lem-trf-flat-module-torsionfree-domain makes its generic fibre nonzero. This
   fibre is finite dimensional over `Ω`; lem-wf-affine-nullstellensatz-vanishing
   gives an `Ω`-point, hence a generic section.
9. The base `Spec A` is normal integral with function field `Ω` by
   lem-weil-pbc-spec-domain-stalks-function-field and the localization lemma.
   The finite-ring-map dictionary makes `Spec E ⟶ Spec A` finite. Apply
   lem-sfb-finite-normal-generic-section-extension to obtain a retraction `E ⟶ A`.
   Its residue map is the prescribed one: both induce the inverse of the same
   structural isomorphism `κ(t) ≅ E/m_E`. Compose to get `C ⟶ B_m` lifting `h`.
10. Clear the denominators of finitely many generator images, using the empty
    product `1` if there are none. They belong to `B[1/f]` with `f ∉ m`.
    All relations hold there because it injects into `B_m`. This yields a map
    `D(f) ⟶ U`, then a section into `Y ×[S] T` by the pullback universal property.
    The residue equality is equality with the given morphism `y`. This uses no
    Noetherian hypothesis on `B` and no quasi-compactness hypothesis on `Y`.
-/
theorem trait_absolute_normalization_local_sections
    (R K Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    Flat (traitAbsoluteNormalizationMap R Ω) ∧
    Surjective (traitAbsoluteNormalizationMap R Ω) ∧
    QuasiCompact (traitAbsoluteNormalizationMap R Ω) ∧
    Presieve.singleton (traitAbsoluteNormalizationMap R Ω) ∈
      Scheme.fpqcPrecoverage (Spec (CommRingCat.of R)) ∧
    (∃ e : Spec (CommRingCat.of Ω) ≅
        (Scheme.Opens.toScheme (X := Spec (CommRingCat.of (integralClosure R Ω)))
          (PrimeSpectrum.basicOpen (algebraMap R (integralClosure R Ω) π))),
      e.hom ≫ (Scheme.Opens.ι (X := Spec (CommRingCat.of (integralClosure R Ω)))
        (PrimeSpectrum.basicOpen (algebraMap R (integralClosure R Ω) π))) =
          Spec.map (CommRingCat.ofHom (integralClosure R Ω).val.toRingHom)) ∧
    (∀ t : Spec (CommRingCat.of (integralClosure R Ω)),
      (t ∈ PrimeSpectrum.basicOpen (algebraMap R (integralClosure R Ω) π) ↔
        ((traitAbsoluteNormalizationMap R Ω) t).asIdeal = ⊥)) ∧
    (∀ t : Spec (CommRingCat.of (integralClosure R Ω)),
      t ∉ PrimeSpectrum.basicOpen (algebraMap R (integralClosure R Ω) π) →
      ((traitAbsoluteNormalizationMap R Ω) t).asIdeal = IsLocalRing.maximalIdeal R ∧
      IsClosed ({t} : Set (Spec (CommRingCat.of (integralClosure R Ω)))) ∧
      IsAlgClosed ((Spec (CommRingCat.of (integralClosure R Ω))).residueField t)) ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R)),
      Flat f → LocallyOfFiniteType f →
      ∀ t : Spec (CommRingCat.of (integralClosure R Ω)),
      ((traitAbsoluteNormalizationMap R Ω) t).asIdeal = IsLocalRing.maximalIdeal R →
      ∀ y : Spec ((Spec (CommRingCat.of (integralClosure R Ω))).residueField t) ⟶
          pullback f (traitAbsoluteNormalizationMap R Ω),
      y ≫ pullback.snd f (traitAbsoluteNormalizationMap R Ω) =
        (Spec (CommRingCat.of (integralClosure R Ω))).fromSpecResidueField t →
      ∃ W : (Spec (CommRingCat.of (integralClosure R Ω))).Opens, t ∈ W ∧
        ∃ (σ : W.toScheme ⟶ pullback f (traitAbsoluteNormalizationMap R Ω))
          (τ : Spec ((Spec (CommRingCat.of (integralClosure R Ω))).residueField t) ⟶
            W.toScheme),
          σ ≫ pullback.snd f (traitAbsoluteNormalizationMap R Ω) = W.ι ∧
          τ ≫ W.ι =
            (Spec (CommRingCat.of (integralClosure R Ω))).fromSpecResidueField t ∧
          τ ≫ σ = y) := by
  sorry

end AlgebraicGeometry
