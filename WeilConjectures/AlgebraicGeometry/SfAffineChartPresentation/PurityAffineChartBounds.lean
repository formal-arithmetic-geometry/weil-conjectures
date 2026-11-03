/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Affine-chart assembly for constructible exceptional inverse image

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
`cor-pur-general-admissibility-datum` (blueprint: cor-pur-general-admissibility-datum).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

open Classical in
open Classical in
open Classical in

/-- The chosen finite affine target cover, finite affine source covers over its members,
and closed affine-space presentations. The equations specify that each presentation is
over its target open. Empty opens and empty index sets are permitted.
Source: blueprint, affine charts in cor-pur-general-admissibility-datum
(blueprint: cor-pur-general-admissibility-datum). -/
structure SfAffineChartPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) where
  count : ℕ
  target : Fin count → Y.Opens
  target_affine : ∀ i, IsAffineOpen (target i)
  target_cover : ∀ y : Y, ∃ i, y ∈ target i
  size : Fin count → ℕ
  source : (i : Fin count) → Fin (size i) → X.Opens
  source_affine : ∀ i j, IsAffineOpen (source i j)
  source_le : ∀ i j, source i j ≤ f ⁻¹ᵁ target i
  source_cover : ∀ (i : Fin count) (x : X), x ∈ f ⁻¹ᵁ target i →
    ∃ j : Fin (size i), x ∈ source i j
  dimension : (i : Fin count) → Fin (size i) → ℕ
  presentation : (i : Fin count) → (j : Fin (size i)) →
    (source i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme
  presentation_closed : ∀ i j, IsClosedImmersion (presentation i j)
  presentation_over : ∀ i j,
    presentation i j ≫
        (AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme ↘
          (target i).toScheme) ≫ (target i).ι = (source i j).ι ≫ f

/-- Omit precisely the empty source charts, retaining the target cover and every
surviving chart's affine-space presentation. The subtype of surviving indices is
reindexed by `Fintype.equivFin`. A point in an original chart witnesses its
nonemptiness, so these charts still cover every inverse image of a target open.
Source: blueprint cor-pur-general-admissibility-datum, omission of empty charts
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.nonemptyCharts
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) :
    SfAffineChartPresentation f :=
  let e (i : Fin C.count) :=
    (Fintype.equivFin {j : Fin (C.size i) // Nonempty (C.source i j)}).symm
  { count := C.count
    target := C.target
    target_affine := C.target_affine
    target_cover := C.target_cover
    size := fun i ↦ Fintype.card {j : Fin (C.size i) // Nonempty (C.source i j)}
    source := fun i j ↦ C.source i (e i j).val
    source_affine := fun i j ↦ C.source_affine i (e i j).val
    source_le := fun i j ↦ C.source_le i (e i j).val
    source_cover := by
      intro i x hx
      obtain ⟨j, hj⟩ := C.source_cover i x hx
      refine ⟨(e i).symm ⟨j, ⟨⟨x, hj⟩⟩⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hj
    dimension := fun i j ↦ C.dimension i (e i j).val
    presentation := fun i j ↦ C.presentation i (e i j).val
    presentation_closed := fun i j ↦ C.presentation_closed i (e i j).val
    presentation_over := fun i j ↦ C.presentation_over i (e i j).val }

/-- Finite-type schemes over a field have finite Krull dimension. This integer-valued
reading takes the nonnegative dimension for a nonempty such scheme and zero for the
empty scheme, whose topological dimension is bottom.
Source: blueprint dimension convention in the affine-chart assembly
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def sfDimension (Y : Scheme.{u}) : ℕ :=
  ((topologicalKrullDim Y).unbotD 0).toNat

/-- The maximum over the nonempty source charts in affine-chart assembly;
the empty source has shift zero.
Source: blueprint cor-pur-general-admissibility-datum, definition of `D`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyDimension
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℕ :=
  if Nonempty X then C.nonemptyCharts.maxDimension else 0

/-- The corollary's integer `c = max_U (c_U + 1 + 2(D-d_U))`, with
`c_U = 2(d_U + dim Y)`. Every summand equals the displayed expression when `X`
is nonempty, after applying `nonemptyCharts`. For the empty source `c = 0`.
Source: blueprint cor-pur-general-admissibility-datum, formula for `c`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyConstant
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℤ :=
  if Nonempty X then
    2 * (C.nonemptyCharts.maxDimension : ℤ) + 2 * (sfDimension Y : ℤ) + 1 else 0

private theorem coefficient_killed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
  let h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    have he := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change Padic.coefficientExtensionAbsoluteValue l E
      (algebraMap ℚ_[l] E (l : ℚ_[l])) = ‖(l : ℚ_[l])‖ at he
    rw [map_natCast] at he
    rw [he]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [← hgen] at hl
  have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl n)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hq

private theorem finite_dimension_bound {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    topologicalKrullDim X ≤
      (((topologicalKrullDim X).unbotD 0).toNat : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  generalize topologicalKrullDim X = t at *
  induction t using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe t =>
    induction t using ENat.recTopCoe with
    | top => exact False.elim ((ENat.natCast_ne_top d)
        (top_le_iff.mp (WithBot.coe_le_coe.mp hd)))
    | coe t => simp

private theorem datum_charP (F : WeilConjectures.FiniteFieldDatum.{u}) : CharP F.k F.p := by
  classical
  let : Fintype F.k₀ := Fintype.ofFinite F.k₀
  let : Fact F.p.Prime := ⟨F.prime⟩
  let : CharP F.k₀ F.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, F.card_base, F.cardinality_eq])
  exact charP_of_injective_algebraMap (algebraMap F.k₀ F.k).injective F.p

private theorem coefficient_invertible
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k)) :
    HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y := by
  let := datum_charP F
  have hlk : (l : F.k) ≠ 0 := by
    intro h
    exact hl ((Nat.prime_dvd_prime_iff_eq F.prime (Fact.out : l.Prime)).mp
      ((CharP.cast_eq_zero_iff F.k F.p l).mp h)).symm
  have hu : IsUnit ((l ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h := ((Ne.isUnit hlk).pow n).map (Scheme.ΓSpecIso (.of F.k)).inv.hom
    simpa only [← Nat.cast_pow, map_natCast] using h.map aY.appTop.hom
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, ?_, hu⟩
  apply ULift.down_injective
  change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
  exact coefficient_killed l E n

end AlgebraicGeometry.Scheme
