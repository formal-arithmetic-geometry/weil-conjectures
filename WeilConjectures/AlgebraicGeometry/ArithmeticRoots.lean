/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicNumberRealization
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.AlgebraicGeometry.WeilNumbers
public import WeilConjectures.AlgebraicGeometry.CommonStageCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactWeilCohomology
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.CharP.CharAndCard

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.AlgebraicGeometry.ArithmeticRootsReciprocalProperties

/-!
# Arithmetic roots of the integral Frobenius factors

Source: Weil conjectures blueprint, `sec-zeta-weil/sk-thm-weil-final/prop-arithmetic-roots`,
statement and proof (blueprint: prop-arithmetic-roots).

The recorded cohomological family is realized over `PadicAlgCl l`. For another chosen
closure `C.Qbar`, a coefficient isomorphism `e` expresses the same ordinary cohomology
by tensor extension, and its Frobenius is the image of the recorded Frobenius under
`ModuleCat.extendScalars e.toRingHom`. The assertion quantifies over every such `e`,
so no identification of closures is imposed as an extra hypothesis. The integral-factor
predicate uses the recorded coefficientwise equality for every prime simultaneously.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The finite-field datum gives characteristic `D.p`, by the existing cardinality criterion.
Source: blueprint `prop-arithmetic-roots.md`, finite-field setting
(blueprint: prop-arithmetic-roots). -/
instance arithmeticRootsBaseCharP (D : FiniteFieldDatum.{u}) : CharP D.k₀ D.p :=
  letI := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))

/-- The coefficient-prime instance required by the recorded cohomological family, obtained
from `C.different` and the finite-field cardinality, without any additional assumption.
Source: blueprint `prop-arithmetic-roots.md`, primes distinct from `p`
(blueprint: prop-arithmetic-roots). -/
instance arithmeticRootsCoefficientChar (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) :
    Fact (ringChar D.k₀ ≠ C.l) :=
  ⟨fun h ↦ C.different (h.symm.trans (ringChar.eq D.k₀ D.p))⟩

/-- The reverse integral factor is monic; its roots are algebraic integers and Weil numbers
of weight `i`, and every adic realization is a reciprocal root and a Frobenius eigenvalue
on ordinary cohomology after scalar extension. Ordinary roots have weight `-i`.
Source: blueprint `sec-zeta-weil/sk-thm-weil-final/prop-arithmetic-roots`, statement and proof
(blueprint: prop-arithmetic-roots).

Proof (the three steps of the DAG node):
1. The reverse of an integer polynomial with constant coefficient one is monic
   (`Polynomial.monic_reverse_of_coeff_zero_eq_one`, `lem-weil-reverse-polynomial-coefficients`).
2. `arithmetic_roots_reciprocal_properties` (`prop-arithmetic-roots-reciprocal-properties`) gives,
   for every reciprocal root, integrality, the intrinsic Weil weight `i`, the root equation of
   every adic realization, and the displayed scalar-extended Frobenius eigenvalue.
3. An ordinary root `β` is nonzero since the constant coefficient is one, so `β⁻¹` is a
   reciprocal root (`Polynomial.mem_roots_reverse_iff`). It lies in `ℚ(β)`; restricting an
   embedding `τ` of `ℚ(β)` to `ℚ(β⁻¹)` and applying step 2 gives `‖τ β‖⁻¹ = q^(i/2)`, hence
   `‖τ β‖ = q^(-i/2)`.
-/
theorem arithmetic_roots (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u}) [X₀.Over (Spec (.of D.k₀))]
    [IsProper (X₀ ↘ Spec (.of D.k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (.of D.k₀))]
    (d : ℕ) (hsmooth : @FiniteFieldDatum.IsSmoothOfPureDimension D
      (Over.mk (X₀ ↘ Spec (.of D.k₀)))
      (inferInstanceAs (LocallyOfFiniteType (X₀ ↘ Spec (.of D.k₀))))
      (inferInstanceAs (QuasiCompact (X₀ ↘ Spec (.of D.k₀)))) d)
    (i : ℤ) (hi₀ : 0 ≤ i) (hi : i ≤ 2 * (d : ℤ))
    (P : Polynomial ℤ) (hP₀ : P.coeff 0 = 1)
    (hP : Scheme.IsIntegralFrobeniusFactor D.k₀ X₀ i P)
    (Qbar : Type v) [Field Qbar] [Algebra ℚ Qbar] [IsAlgClosure ℚ Qbar] :
    P.reverse.Monic ∧
      (∀ α : Qbar, (P.reverse.map (Int.castRingHom Qbar)).IsRoot α →
        IsIntegral ℤ α ∧ IsWeilNumber D α (i : ℝ) ∧
          ∀ (C : D.CoefficientDatum)
            (e : PadicAlgCl C.l ≃ₐ[Padic C.l] C.Qbar)
            (j : C.AlgebraicNumberRealization D Qbar),
            ((AlgEquiv.toEquiv j) α : C.Qbar) ≠ 0 ∧
              ((Scheme.frobeniusCharpolyRev D.k₀ C.l X₀ i).map e.toRingHom).IsRoot
                ((AlgEquiv.toEquiv j) α : C.Qbar)⁻¹ ∧
              Module.End.HasEigenvalue
                (((ModuleCat.extendScalars e.toRingHom).map
                  (ModuleCat.ofHom
                    (WeilSheaf.ordinaryCompactWeilSheafCohomology
                      (WeilSheaf.adicConstant D.k₀ C.l X₀) i).1.frobeniusEnd)).hom)
                ((AlgEquiv.toEquiv j) α : C.Qbar)) ∧
      ∀ β : Qbar, (P.map (Int.castRingHom Qbar)).IsRoot β →
        ∀ τ : IntermediateField.adjoin ℚ ({β} : Set Qbar) →+* ℂ,
          ‖τ (IntermediateField.AdjoinSimple.gen ℚ β)‖ =
            (D.q : ℝ) ^ (-(i : ℝ) / 2) := by
  classical
  have : CharZero Qbar := algebraRat.charZero Qbar
  have hrecip := arithmetic_roots_reciprocal_properties D X₀ d hsmooth i hi₀ hi P hP₀ hP
    Qbar
  refine ⟨Polynomial.monic_reverse_of_coeff_zero_eq_one hP₀, hrecip, ?_⟩
  intro β hβ τ
  let R := P.map (Int.castRingHom Qbar)
  have hR₀ : R.coeff 0 = 1 := by simp [R, hP₀]
  have hR : R ≠ 0 := by intro h; simp [h] at hR₀
  have hβne : β ≠ 0 := by
    intro h
    subst β
    have h := hβ
    change R.IsRoot 0 at h
    simp [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hR₀] at h
  have hα : (P.reverse.map (Int.castRingHom Qbar)).IsRoot β⁻¹ := by
    rw [← Polynomial.reverse_map (RingHom.injective_int _) P]
    exact Polynomial.isRoot_of_mem_roots ((Polynomial.mem_roots_reverse_iff hR).2
      ⟨inv_ne_zero hβne, by simpa using hβ⟩)
  have hw := (hrecip β⁻¹ hα).2.1.2
  have hmem : β⁻¹ ∈ IntermediateField.adjoin ℚ ({β} : Set Qbar) :=
    IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℚ β)
  have hle : IntermediateField.adjoin ℚ ({β⁻¹} : Set Qbar) ≤
      IntermediateField.adjoin ℚ ({β} : Set Qbar) :=
    IntermediateField.adjoin_simple_le_iff.2 hmem
  let incl : IntermediateField.adjoin ℚ ({β⁻¹} : Set Qbar) →+*
      IntermediateField.adjoin ℚ ({β} : Set Qbar) :=
    { toFun := fun a ↦ ⟨a.val, hle a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hn := hw (τ.comp incl)
  have hgen : (⟨β⁻¹, hmem⟩ : IntermediateField.adjoin ℚ ({β} : Set Qbar)) =
      (IntermediateField.AdjoinSimple.gen ℚ β)⁻¹ := rfl
  change ‖τ (⟨β⁻¹, hmem⟩ : IntermediateField.adjoin ℚ ({β} : Set Qbar))‖ = _ at hn
  rw [hgen, map_inv₀, norm_inv] at hn
  rw [neg_div, Real.rpow_neg (Nat.cast_nonneg D.q), ← hn, inv_inv]

end WeilConjectures
