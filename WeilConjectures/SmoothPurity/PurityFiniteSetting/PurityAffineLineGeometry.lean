/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
import WeilConjectures.AlgebraicGeometry.Open.OpenComplementKnown
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IntermediateField.Algebraic
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-! # Affine-line dimension, open complement and localization comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

private theorem finite_base_subfield (P : PurityFiniteSetting.{u}) :
    ∃ k₀ : Subfield P.field.k, Finite k₀ ∧ IsAlgClosure k₀ P.field.k := by
  let F : IntermediateField P.field.k₀ P.field.k := ⊥
  have : Finite F := Finite.of_equiv P.field.k₀
    (IntermediateField.botEquiv P.field.k₀ P.field.k).symm.toEquiv
  refine ⟨F.toSubfield, this, ?_⟩
  refine ⟨IsAlgClosure.isAlgClosed P.field.k₀, ?_⟩
  change Algebra.IsAlgebraic F P.field.k
  infer_instance

/-- Finite type bounds the dimension; the complement theorem supplies the open bound.
Source: affine-line boundary node, step 1.
(blueprint: lem-pur-affine-line-boundary-geometry). -/
theorem affine_line_boundary_geometry (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ (d : ℕ) (hj : QuasiCompact (openImmersion Y)),
      topologicalKrullDim (Line Y) ≤ (d : WithBot ℕ∞) ∧
      @Scheme.HasOpenComplementCondition P.Coefficient inferInstance inferInstance
        (Punctured Y) (Line Y) (openImmersion Y) inferInstance hj (2 * d) := by
  let : LocallyOfFiniteType (lineProjection Y) := inferInstanceAs
    (LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  let : QuasiCompact (lineProjection Y) := inferInstanceAs
    (QuasiCompact ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  let : IsLocallyNoetherian (Line Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (lineProjection Y ≫ a)
  let : QuasiCompact (openImmersion Y) := by
    change QuasiCompact ((Line Y).basicOpen (coordinate Y)).ι
    infer_instance
  let : (Line Y).Over (Spec (.of P.field.k)) := ⟨lineProjection Y ≫ a⟩
  let : LocallyOfFiniteType ((Line Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (lineProjection Y ≫ a))
  let : QuasiCompact ((Line Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (lineProjection Y ≫ a))
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (lineProjection Y ≫ a)
  refine ⟨d, inferInstance, hd, ?_⟩
  have hc : P.coefficients.l ≠ ringChar P.field.k := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    let : Fact P.field.p.Prime := ⟨P.field.prime⟩
    let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    let : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    simpa only [ringChar.eq P.field.k P.field.p] using P.coefficients.different
  exact (Scheme.hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension
    P.field.k (finite_base_subfield P) d hd (openImmersion Y) P.Coefficient
    P.coefficients.l (Fact.out : P.coefficients.l.Prime) hc
    ⟨P.kummerLevel, by simpa only [Nat.smul_one_eq_cast, exponent] using
      P.exponent_coefficient_eq_zero h⟩).1

/-- The finite-type zero section and its coordinate complement satisfy the hypotheses
of the recorded localization-comparison theorem.
Source: affine-line boundary realization, step 1; zero-section complement.
(blueprint: lem-pur-affine-line-boundary-geometry). -/
theorem affine_line_boundary_comparison (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    Nonempty (Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) := by
  let : LocallyOfFiniteType (lineProjection Y) := inferInstanceAs
    (LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  let : QuasiCompact (lineProjection Y) := inferInstanceAs
    (QuasiCompact ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  let : IsSeparated (lineProjection Y) := inferInstanceAs
    (IsSeparated ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  let : Y.Over (Spec (.of P.field.k)) := ⟨a⟩
  let : IsSeparated (Y ↘ Spec (.of P.field.k)) := inferInstanceAs (IsSeparated a)
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType a)
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact a)
  let : (Line Y).Over (Spec (.of P.field.k)) := ⟨lineProjection Y ≫ a⟩
  let : IsSeparated ((Line Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (IsSeparated (lineProjection Y ≫ a))
  let : LocallyOfFiniteType ((Line Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (lineProjection Y ≫ a))
  let : QuasiCompact ((Line Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (lineProjection Y ≫ a))
  let : (lineProjection Y).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  obtain ⟨_, hj, _, _⟩ := affine_line_boundary_geometry P h Y a
  let := hj
  apply exists_comparison P (lineProjection Y) (zeroSection Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y) (openImmersion Y)
  rw [show Set.range (openImmersion Y).base = (Set.range (zeroSection Y).base)ᶜ from
    AffineSpace.range_basicOpen_ι_coord Y]
  exact isCompl_compl
end WeilConjectures.PurityFiniteSetting
