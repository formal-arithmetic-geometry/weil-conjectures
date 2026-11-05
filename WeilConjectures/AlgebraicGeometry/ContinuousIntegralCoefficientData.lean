/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Integral continuous coefficients and their two coefficient maps

Source: Bhatt--Scholze, Section 6.8; Mathlib's `NormedField.valuation.integer`.
The integral ring is the closed unit ball in the given normed extension, with its subspace
topology. The residue ring has the quotient topology. Both maps are actual continuous ring
maps; the induced functors are the existing derived extensions of scalars.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The valuation ring of the given norm on E. Source: NormedValued.lean
(auxiliary; not a blueprint node). -/
noncomputable def continuousIntegers : Subring E :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  (NormedField.valuation (K := E)).integer

/-- E is obtained from its valuation ring by inverting ℓ. Clear the norm of an
element by a sufficiently large power of ℓ, using ‖ℓ‖ < 1.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
instance continuousIntegers_isLocalization :
    IsLocalization.Away (ℓ : continuousIntegers ℓ E) E := by
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hnorm : ‖(ℓ : E)‖ < 1 := by
    have h : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ℓ : ℚ_[ℓ]))
    rw [h]
    exact Padic.norm_p_lt_one
  apply IsLocalization.Away.mk
  · change IsUnit (ℓ : E)
    exact isUnit_iff_ne_zero.mpr hp
  · intro s
    by_cases hs : s = 0
    · subst s
      exact ⟨0, 0, by simp⟩
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (inv_pos.mpr (norm_pos_iff.mpr hs)) hnorm
    have hmem : s * (ℓ : E) ^ n ∈ continuousIntegers ℓ E := by
      change ‖s * (ℓ : E) ^ n‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_mul, norm_pow]
      calc
        ‖s‖ * ‖(ℓ : E)‖ ^ n ≤ ‖s‖ * ‖s‖⁻¹ :=
          (mul_lt_mul_of_pos_left hn (norm_pos_iff.mpr hs)).le
        _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hs)
    exact ⟨n, ⟨_, hmem⟩, rfl⟩
  · intro a b hab
    have h : a = b := Subtype.ext hab
    subst b
    exact ⟨0, rfl⟩

/-- Continuous E-valued functions on a compact space are obtained from the integral
functions by inverting the constant function ℓ. Compactness gives one denominator for
the entire function, including for an empty space.
Source: Bhatt--Scholze, Section 6.8, localization of continuous coefficient sheaves
(auxiliary; not a blueprint node). -/
theorem continuousIntegralFunctions_isLocalization
    (S : Type u) [TopologicalSpace S] [CompactSpace S] :
    letI := ((continuousIntegers ℓ E).subtype.compLeftContinuous S
      continuous_subtype_val).toAlgebra
    IsLocalization.Away (ContinuousMap.const S (ℓ : continuousIntegers ℓ E)) C(S, E) := by
  let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S continuous_subtype_val
  let := φ.toAlgebra
  change IsLocalization.Away (ContinuousMap.const S (ℓ : continuousIntegers ℓ E)) C(S, E)
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hnorm : ‖(ℓ : E)‖ < 1 := by
    have h : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ℓ : ℚ_[ℓ]))
    rw [h]
    exact Padic.norm_p_lt_one
  apply IsLocalization.Away.mk
  · exact (isUnit_iff_ne_zero.mpr hp).map (ContinuousMap.C : E →+* C(S, E))
  · intro f
    have hb : 0 < ‖f‖ + 1 := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hb) hnorm
    have hmem (x : S) : f x * (ℓ : E) ^ n ∈ continuousIntegers ℓ E := by
      change ‖f x * (ℓ : E) ^ n‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_mul, norm_pow]
      calc
        ‖f x‖ * ‖(ℓ : E)‖ ^ n ≤ (‖f‖ + 1) * ‖(ℓ : E)‖ ^ n :=
          mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x |>.trans (by linarith))
            (by positivity)
        _ ≤ (‖f‖ + 1) * (‖f‖ + 1)⁻¹ := (mul_lt_mul_of_pos_left hn hb).le
        _ = 1 := mul_inv_cancel₀ hb.ne'
    let a : C(S, continuousIntegers ℓ E) :=
      ⟨fun x ↦ ⟨f x * (ℓ : E) ^ n, hmem x⟩,
        (f.continuous.mul continuous_const).subtype_mk _⟩
    exact ⟨n, a, rfl⟩
  · intro a b hab
    have h : a = b := by
      ext x
      exact congrArg (fun f : C(S, E) ↦ f x) hab
    subst b
    exact ⟨0, rfl⟩

/-- Continuous integral coefficients, pulled from the profinite point.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable abbrev integralCoeff := Profinite.continuousMapRingObj.{u} (continuousIntegers ℓ E)

/-- The quotient of the valuation ring by the ideal generated by ℓ.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable abbrev integralResidue :=
  (continuousIntegers ℓ E) ⧸ Ideal.span {(ℓ : continuousIntegers ℓ E)}

/-- The quotient by ℓ has discrete topology: its defining ideal contains the open
ball of radius ‖ℓ‖. Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
instance integralResidue_discreteTopology : DiscreteTopology (integralResidue ℓ E) := by
  let I : Ideal (continuousIntegers ℓ E) := Ideal.span {(ℓ : continuousIntegers ℓ E)}
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hopen : IsOpen (I : Set (continuousIntegers ℓ E)) := by
    apply I.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    have ho : IsOpen ((fun x : continuousIntegers ℓ E ↦ (x : E)) ⁻¹'
        Metric.ball 0 ‖(ℓ : E)‖) := Metric.isOpen_ball.preimage continuous_subtype_val
    apply Filter.mem_of_superset (ho.mem_nhds (by
      change dist (0 : E) 0 < ‖(ℓ : E)‖
      simpa only [dist_self] using norm_pos_iff.mpr hp))
    intro x hx
    have hx' : ‖(x : E)‖ < ‖(ℓ : E)‖ := by
      change dist (x : E) 0 < ‖(ℓ : E)‖ at hx
      simpa only [dist_zero_right] using hx
    have hdiv : (x : E) / ℓ ∈ continuousIntegers ℓ E := by
      change ‖(x : E) / ℓ‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hp)).2 hx'.le
    change x ∈ Ideal.span {(ℓ : continuousIntegers ℓ E)}
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(x : E) / ℓ, hdiv⟩, ?_⟩
    apply Subtype.ext
    change (x : E) = (ℓ : E) * ((x : E) / ℓ)
    exact (mul_div_cancel₀ _ hp).symm
  exact QuotientAddGroup.discreteTopology hopen

/-- The integral residue ring is finite for a finite normed extension. The integral
ring is compact and its quotient is discrete. Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
instance integralResidue_finite [FiniteDimensional ℚ_[ℓ] E] : Finite (integralResidue ℓ E) := by
  let : ProperSpace E := FiniteDimensional.proper ℚ_[ℓ] E
  have hball : (continuousIntegers ℓ E : Set E) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    simp only [dist_zero_right, ← NNReal.coe_le_coe, NNReal.coe_one]
    rfl
  let : CompactSpace (continuousIntegers ℓ E) :=
    isCompact_iff_compactSpace.mp (hball ▸ isCompact_closedBall 0 1)
  exact finite_of_compact_of_discrete

/-- The actual continuous quotient map on condensed ring objects.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable def integralReductionMap :
    integralCoeff.{u} ℓ E ⟶ Profinite.continuousMapRingObj (integralResidue ℓ E) :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap
      (Ideal.Quotient.mk (Ideal.span {(ℓ : continuousIntegers ℓ E)}))
      continuous_quot_mk)
instance : IsMonHom (integralReductionMap.{u} ℓ E) := by
  dsimp [integralReductionMap]
  infer_instance

/-- The residue quotient as an actual morphism of integral module objects.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable def integralQuotientLinear : Mod.regular (integralCoeff.{u} ℓ E) ⟶
    (Mod.comap (integralReductionMap ℓ E)).obj
      (Mod.regular (Profinite.continuousMapRingObj (integralResidue ℓ E))) :=
  Mod.homMk (integralReductionMap ℓ E) (by
    change μ[integralCoeff ℓ E] ≫ integralReductionMap ℓ E =
      (integralCoeff ℓ E) ◁ integralReductionMap ℓ E ≫
        (integralReductionMap ℓ E ▷ _) ≫ μ[_]
    rw [IsMonHom.mul_hom, tensorHom_def']
    exact Category.assoc _ _ _)

/-- The derived category with the finite quotient coefficients.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable abbrev integralResidueDerived (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj (integralResidue ℓ E)) X))

/-- Derived reduction modulo ℓ over the coefficient ring pulled to X.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable def integralReduction (X : Scheme.{u}) :=
  L(Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))

/-- The continuous inclusion of the valuation ring into E on condensed rings.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable def integralScalarMap :
    integralCoeff.{u} ℓ E ⟶ Profinite.continuousMapRingObj E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap (continuousIntegers ℓ E).subtype continuous_subtype_val)
instance : IsMonHom (integralScalarMap.{u} ℓ E) := by
  dsimp [integralScalarMap]
  infer_instance

/-- Derived inversion of ℓ followed by continuous E coefficients on X.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable def integralScalarExtension (X : Scheme.{u}) :=
  L(Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))
end AlgebraicGeometry.ProEtale.CondensedRing
