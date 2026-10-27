/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtensionData
public import Sheaf.Paper.GlobalGeometricFrobenius
import Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Sheaf.Paper.NormalizedStageCoefficientCalculus
import Sheaf.Paper.CoefficientMapGeometricSquares

/-! # Finite free coefficient extensions and cofinal levels

The canonical functors and comparison maps are publicly re-exported from the data module.
Source: blueprint, lem-coef-finite-free-extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem stage_ramification (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s : Stage l E) :
    ∃ (e : ℕ+) (z : s.integersˣ),
      s.parameter = (z : s.integers) * Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
      (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
        Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
      ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ) := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have : IsDiscreteValuationRing s.integers := hF.2.2.2.2.2.2.2.1
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenF : Ideal.span {Padic.coefficientExtensionUniformizer l s.field} =
      Padic.coefficientExtensionMaximalIdeal l s.field :=
    hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπE : Padic.coefficientExtensionUniformizer l E ≠ 0 :=
    ((hE.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.2.2 _).mp
      hgenE).1
  have hπF : Irreducible (Padic.coefficientExtensionUniformizer l s.field) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    exact (hF.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal s.integers)).trans hgenF.symm
  have hparam : s.parameter ≠ 0 := by
    intro h
    apply hπE
    apply Subtype.ext
    apply s.inclusion.injective
    change s.inclusion (Padic.coefficientExtensionUniformizer l E : E) = s.inclusion 0
    exact (congrArg Subtype.val h).trans (map_zero s.inclusion).symm
  have hlt : Padic.coefficientExtensionAbsoluteValue l s.field (s.parameter : s.field) < 1 := by
    have hmap : spectralNorm (Padic l) s.field
        (s.inclusion (Padic.coefficientExtensionUniformizer l E : E)) =
        spectralNorm (Padic l) E (Padic.coefficientExtensionUniformizer l E : E) := by
      unfold spectralNorm
      rw [minpoly.algHom_eq s.inclusion s.inclusion.injective]
    change spectralNorm (Padic l) s.field
      (s.inclusion (Padic.coefficientExtensionUniformizer l E : E)) < 1
    rw [hmap]
    apply (hE.2.1 _).mp
    change Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨e, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hparam hπF
  have he : 0 < e := by
    by_contra hn
    have heq : e = 0 := by omega
    have hu : IsUnit s.parameter := by
      rw [hz, heq, pow_zero, mul_one]
      exact z.isUnit
    have habs := (hF.2.2.1 s.parameter).mp hu
    linarith
  refine ⟨⟨e, he⟩, z, hz, ?_, ?_⟩
  · intro n
    rw [hz, Ideal.span_singleton_mul_left_unit z.isUnit,
      ← Ideal.span_singleton_pow, ← pow_mul]
    rfl
  · intro r
    refine ⟨⟨r + 1, Nat.succ_pos r⟩, ?_⟩
    exact (Nat.le_succ r).trans (by
      simpa using Nat.mul_le_mul_right (r + 1) (show 1 ≤ e by omega))

private theorem arrow_finite_free (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s t : Stage l E) (a : Arrow s t)
    (h : s.exponent = t.exponent) : a.IsFiniteFree := by
  classical
  let A := s.integers
  let B := t.integers
  let φ : A →+* B := strictEtaleIntegerMap l a.embedding
  let : Algebra s.field t.field := a.embedding.toRingHom.toAlgebra
  let : Algebra A t.field := (a.embedding.toRingHom.comp A.subtype).toAlgebra
  let : Algebra A B := φ.toAlgebra
  have : IsScalarTower A s.field t.field := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B t.field := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) s.field t.field :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (a.embedding.commutes x).symm
  have : FiniteDimensional s.field t.field :=
    Module.Finite.of_restrictScalars_finite (Padic l) s.field t.field
  have hA := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have : IsFractionRing A s.field := hA.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := hA.2.2.2.2.2.2.2.2.1
  have : CharZero s.field :=
    charZero_of_injective_algebraMap (algebraMap (Padic l) s.field).injective
  have : IsIntegralClosure B A t.field := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure A t.field ↔ ∃ y : B, (y : t.field) = x
    rw [← Padic.padic_integers_integralClosure l s.field t.field a.embedding x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.Finite A B := IsIntegralClosure.finite A s.field t.field B
  have : Module.Free A B := IsIntegralClosure.module_free A s.field t.field B
  have hparam : φ s.parameter = t.parameter := by
    apply Subtype.ext
    change a.embedding (s.inclusion _) = t.inclusion _
    exact DFunLike.congr_fun a.over_base _
  have hmap : s.ideal.map (algebraMap A B) = t.ideal := by
    change Ideal.map φ _ = _
    simp only [Stage.ideal, Ideal.map_pow, Ideal.map_span, Set.image_singleton, hparam, h]
    rfl
  let : Algebra s.ring t.ring := a.ringMap.toAlgebra
  let e : (B ⧸ s.ideal.map (algebraMap A B)) ≃ₗ[s.ring] t.ring :=
    (Ideal.quotEquivOfEq hmap).toAddEquiv.toLinearEquiv (by
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl)
  let b : Module.Basis (Fin (Module.finrank A B)) s.ring t.ring :=
    ((Module.finBasis A B).baseChange s.ring).map
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B s.ideal).symm.toLinearEquiv.trans e)
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b⟩

/-- Finite free coefficient extensions on the cofinal ramified levels, including all five
canonical comparisons on both small sites, all coefficient cocycles and the scheme-isomorphism
squares. The index `Stage` uses the base uniformizer, so ramification is retained.
Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-free-extension (blueprint: lem-coef-finite-free-extension).

Proof: spectral norm is preserved by the field embedding, so the base uniformizer
is nonzero and belongs to the maximal ideal of the extension DVR. Factor it as a
unit times a positive power of the upper uniformizer. Powers of principal ideals
give the ideal equality; positivity gives cofinality by choosing n = r + 1.

For an equal-exponent arrow, identify the upper valuation ring with the integral
closure of the lower DVR in the finite characteristic-zero field extension. This
integral closure is finite and free. Base change of a finite basis to the quotient,
followed by the quotient--tensor isomorphism, gives the required basis; the
parameter image equation identifies the module action with the actual Arrow map.

Apply lem-sf-normalized-stage-coefficient-calculus to obtain the two normalized
packages. For each stage arrow apply lem-sf-coefficient-map-geometric-squares to
its ring map and the package's normalized pro-etale tensorator. Combine its eight
squares with the two canonical-map equations from the normalized calculus. -/
theorem finite_free_coefficient_extension (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ s : Stage l E, ∃ (e : ℕ+) (z : s.integersˣ),
      s.parameter = (z : s.integers) * Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
      (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
        Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
      ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ)) ∧
    (∀ (s t : Stage l E) (a : Arrow s t), s.exponent = t.exponent → a.IsFiniteFree) ∧
    (∀ (T X Z : Scheme.{u})
      [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
      [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
      [QuasiCompact (T ↘ Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
      [QuasiCompact (X ↘ Spec (.of D.k))]
      [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
      [QuasiCompact (Z ↘ Spec (.of D.k))]
      (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
      (c : Compactification (X ↘ Spec (.of D.k))),
      ∃ (et : Sites.Calculus false l E f i c) (pro : Sites.Calculus true l E f i c),
        Sites.Normalized l E f i c et pro ∧
        ∀ {s t : Stage l E} (a : Arrow s t),
          Sites.DirectGeometry a.ringMap f ∧ Sites.HomGeometry a.ringMap X ∧
          Sites.ClosedGeometry a.ringMap i ∧
          Sites.ExceptionalGeometry a.ringMap c (𝟙_ _) ∧
          Sites.ProDirectGeometry a.ringMap f ∧
          Sites.ProClosedGeometry a.ringMap i ∧
          Sites.ProHomGeometry a.ringMap X (pro.tensorIso a) ∧
          Sites.ProOmegaGeometry a.ringMap c ∧
          (∀ M : Sites.D true s.ring X, Sites.Ctf true s.ring X M →
            pro.closedMap a M = Sites.proClosedMap a.ringMap i M) ∧
          pro.omegaMap a = Sites.proOmegaMap a.ringMap c) := by
  refine ⟨stage_ramification l E, arrow_finite_free l E, ?_⟩
  intro T X Z _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ i _ _ c
  obtain ⟨et, pro, hn, hc, hw⟩ :=
    normalized_stage_coefficient_calculus D l _hl E T X Z f i c
  refine ⟨et, pro, hn, ?_⟩
  intro s t a
  obtain ⟨hd, hh, hcl, he, hpd, hpc, hph, hpo⟩ :=
    coefficient_map_geometric_squares s.ring t.ring a.ringMap f i c
      (pro.tensorIso a) (pro.tensor_normalized a)
  exact ⟨hd, hh, hcl, he, hpd, hpc, hph, hpo, hc a, hw a⟩

end WeilConjectures.FiniteFreeCoefficients
