/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularHilbertCoefficientData
public import WeilConjectures.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
public import WeilConjectures.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.AlgebraicGeometry.MarkedIdealOrder
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace

import WeilConjectures.AlgebraicGeometry.FormalDivisionScalarExtension
import WeilConjectures.AlgebraicGeometry.FormalJetLengthScalarExtension


/-! # Formal coefficient strata and their three transforms

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
Theorem 7.14, Theorems 7.20--7.21, Remarks 9.5 and proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion).

The chart substitutions and division operators below are actual coefficient formulas.
Saturation is contraction from localization, and the regular assertions use the existing
scheme-theoretic strict transform. No arbitrary comparison morphism is assumed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertCoefficient

/-- The coefficient order locus on the specified regular coefficient scheme.
Source: BM 1997, Remark 9.5(1)
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def RegularHilbertCoefficientDatum.orderLocus
    {k : Type u} [Field k] {X M : Scheme.{u}}
    {p : M ⟶ Spec (.of k)} {i : X ⟶ M} {a : X} {m n s Q : ℕ}
    {α : Fin s → Fin n →₀ ℕ} (D : RegularHilbertCoefficientDatum p i a m n s α Q) :
    Set D.N :=
  {b | ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
    D.N.presheaf.germ ⊤ b (by trivial) (D.coeff l γ) ∈
      IsLocalRing.maximalIdeal (D.N.presheaf.stalk b) ^ ((α l).degree - γ.degree)}

/-- The centered substitution in a denominator chart of a coordinate blowup.
The denominator has homogeneous coordinate one; only the other direction entries are used.
Source: BM 1997, (7.18), proof of Theorem 7.20
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientBlowupVariables {σ : Type} [DecidableEq σ]
    {L : Type u} [Field L] (J : Finset σ) (h : σ) (ξ : σ → L) :
    σ → MvPowerSeries σ L :=
  fun j ↦ if j = h then MvPowerSeries.X h else
    if j ∈ J then MvPowerSeries.X h * (MvPowerSeries.C (ξ j) + MvPowerSeries.X j)
    else MvPowerSeries.X j

/-- Remove a prescribed power of one variable by shifting coefficients.
The transform theorem asserts divisibility, so this is actual exact division there.
Source: BM 1997, (7.18)--(7.19)
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientDivide {σ : Type} [DecidableEq σ] {L : Type u} [Field L]
    (h : σ) (d : ℕ) (f : MvPowerSeries σ L) : MvPowerSeries σ L :=
  fun δ ↦ MvPowerSeries.coeff (δ + Finsupp.single h d) f

/-- Total transform under the explicit continuous chart substitution.
Source: BM 1997, (7.18), Theorems 7.20--7.21
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientTotalTransform {σ : Type} [DecidableEq σ]
    {L : Type u} [Field L] (J : Finset σ) (h : σ) (ξ : σ → L)
    (K : Ideal (MvPowerSeries σ L)) : Ideal (MvPowerSeries σ L) :=
  Ideal.span
    (MvPowerSeries.subst (coefficientBlowupVariables J h ξ) '' (K : Set (MvPowerSeries σ L)))

/-- Scheme-theoretic saturation by the exceptional equation, as localization contraction.
Source: BM 1997, (7.18); ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientStrictTransform {σ : Type} [DecidableEq σ]
    {L : Type u} [Field L] (J : Finset σ) (h : σ) (ξ : σ → L)
    (K : Ideal (MvPowerSeries σ L)) : Ideal (MvPowerSeries σ L) :=
  Ideal.comap (algebraMap _ (Localization.Away (MvPowerSeries.X h : MvPowerSeries σ L)))
    ((coefficientTotalTransform J h ξ K).map
      (algebraMap _ (Localization.Away (MvPowerSeries.X h : MvPowerSeries σ L))))

/-- The permissible center consists of some coefficient variables and all transverse variables.
Source: BM 1997, proof of Theorem 7.20, Case I
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientCenterVariables {m n : ℕ} (Y : Finset (Fin m)) :
    Finset (Fin m ⊕ Fin n) :=
  Y.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

/-- Weighted coefficient transform; negative weights mean multiplication.
For positive weights the theorem below asserts the exact division identity.
Source: BM 1997, Theorem 7.20(3)(ii), proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientWeightedTransform {m n : ℕ} {L : Type u} [Field L]
    (Y : Finset (Fin m)) (h : Fin m) (ξ : Fin m → L)
    (d : ℕ) (γ : Fin n →₀ ℕ) (c : MvPowerSeries (Fin m) L) :
    MvPowerSeries (Fin m) L :=
  if γ.degree < d then
    coefficientDivide h (d - γ.degree)
      (MvPowerSeries.subst (coefficientBlowupVariables Y h ξ) c)
  else MvPowerSeries.X h ^ (γ.degree - d) *
    MvPowerSeries.subst (coefficientBlowupVariables Y h ξ) c

/-- The Hilbert equality germ is exactly the image of the regular coefficient order locus.
No reducedness is required when the five conditions are supplied as data.
Source: BM 1997, Theorem 7.14, Remarks 9.5(1)--(2), proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG steps 1--2 and 14. Supported homogeneous division identifies H_K with H_D.
The minors theorem identifies the equality germ with the low derivative ideal.
The invertible block Jacobians generate (Z). Modulo (Z), derivatives are factorials
 times W derivatives of the regular coefficients. Thus their vanishing is exactly the
stated local orders. The jet theorem supplies finitely many local function values on X.
At nonclosed points use the residue-field diagonal Taylor map, faithful flatness and
coherent descent from the implicit Taylor calculus; this retains all ambient variables. -/
theorem coefficient_equality_germ {k : Type u} [Field k] [CharZero k]
    {X M : Scheme.{u}} (p : M ⟶ Spec (.of k)) (i : X ⟶ M)
    [IsClosedImmersion i] [Smooth p] [LocallyOfFiniteType (i ≫ p)]
    [QuasiCompact (i ≫ p)] (a : X) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum p i a m n s α Q) :
    ∃ V : D.U.Opens, D.center ∈ V ∧ ∀ y : D.U, y ∈ V →
      ((∃ x : pullback (C := Scheme.{u}) i D.e, pullback.snd i D.e x = y ∧
          HilbertSamuel.function (pullback.snd i D.e ≫ D.e ≫ p) x =
            HilbertSamuel.function (i ≫ p) a) ↔ y ∈ D.j '' D.orderLocus) := by
  sorry

/-- All denominator charts of a permissible blowup, including directions missing N'.
The center-order hypothesis is the formal version of containment of the smooth center
in the coefficient order locus. The localization contraction is the saturated strict
transform, rather than a uniform controlled transform.
Source: BM 1997, Theorem 7.20 and proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG steps 1 and 3--12. Center containment gives c_igamma in (Y)^(d_i-|gamma|).
The supported quotient order estimate makes the individual divided generators regular
and generates the saturation. Compare finite jet ranks after scaling to get nonincrease.
The homogeneous restriction test gives the prefix division bases. Translated homogeneous
minors force strict drop in every normal direction. In a tangent chart, order retention
forces all transverse direction entries to vanish. The transformed Jacobian and derivative
identities preserve conditions (1),(2),(4),(5). Supported quotient estimates and closedness
of the supported image give (3). If an order drops, its first dropping block contributes
an independent relation below its vertex degree, so equality fails. Extracting each Z
coefficient gives the weighted formula, and the order test is coefficientwise.
These are finite jet matrix identities over any characteristic-zero field, in particular
any extension of the original residue field; the empty family and zero center are included. -/
theorem coefficient_permissible_chart {L : Type u} [Field L] [CharZero L]
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (pick : Fin n → Fin s) (β : Fin n → Fin n →₀ ℕ)
    (hpick : ∀ j : Fin n, α (pick j) = β j + Finsupp.single j 1)
    (hprefix : ∀ (q : ℕ) (j : Fin n), essential α q j → (α (pick j)).degree ≤ q)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (K : Ideal (MvPowerSeries (Fin m ⊕ Fin n) L))
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hf : formalConditions α pick β Q K f) (Y : Finset (Fin m))
    (hC : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      implicitTransverseCoeff γ (f l) ∈
        (Ideal.span (MvPowerSeries.X '' (Y : Set (Fin m)))) ^ ((α l).degree - γ.degree))
    (h : Fin m ⊕ Fin n) (hh : h ∈ coefficientCenterVariables Y)
    (ξ : (Fin m ⊕ Fin n) → L) :
    (∀ l : Fin s, MvPowerSeries.X h ^ (α l).degree *
        coefficientDivide h (α l).degree
          (MvPowerSeries.subst (coefficientBlowupVariables (coefficientCenterVariables Y) h ξ)
            (f l)) =
      MvPowerSeries.subst (coefficientBlowupVariables (coefficientCenterVariables Y) h ξ)
        (f l)) ∧
    coefficientStrictTransform (coefficientCenterVariables Y) h ξ K =
      Ideal.span (Set.range fun l : Fin s ↦ coefficientDivide h (α l).degree
        (MvPowerSeries.subst (coefficientBlowupVariables (coefficientCenterVariables Y) h ξ)
          (f l))) ∧
    (∀ q : ℕ, extendedHilbert
        (coefficientStrictTransform (coefficientCenterVariables Y) h ξ K) q ≤
      extendedHilbert K q) ∧
    (extendedHilbert (coefficientStrictTransform (coefficientCenterVariables Y) h ξ K) =
        extendedHilbert K ↔
      ∃ hW : Fin m, h = Sum.inl hW ∧ (∀ j : Fin n, ξ (Sum.inr j) = 0) ∧
        ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
          ((α l).degree - γ.degree : ℕ) ≤
            (coefficientWeightedTransform Y hW (fun j ↦ ξ (Sum.inl j))
              (α l).degree γ (implicitTransverseCoeff γ (f l))).order) ∧
    (extendedHilbert (coefficientStrictTransform (coefficientCenterVariables Y) h ξ K) =
        extendedHilbert K →
      formalConditions α pick β Q
        (coefficientStrictTransform (coefficientCenterVariables Y) h ξ K)
        (fun l ↦ coefficientDivide h (α l).degree
          (MvPowerSeries.subst (coefficientBlowupVariables (coefficientCenterVariables Y) h ξ)
            (f l)))) ∧
    (∀ hW : Fin m, h = Sum.inl hW → (∀ j : Fin n, ξ (Sum.inr j) = 0) →
      (∀ (l : Fin s) (γ : Fin n →₀ ℕ),
        implicitTransverseCoeff γ (coefficientDivide h (α l).degree
          (MvPowerSeries.subst (coefficientBlowupVariables (coefficientCenterVariables Y) h ξ)
            (f l))) =
        coefficientWeightedTransform Y hW (fun j ↦ ξ (Sum.inl j))
          (α l).degree γ (implicitTransverseCoeff γ (f l))) ∧
      ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
        MvPowerSeries.X hW ^ ((α l).degree - γ.degree) *
          coefficientWeightedTransform Y hW (fun j ↦ ξ (Sum.inl j))
            (α l).degree γ (implicitTransverseCoeff γ (f l)) =
        MvPowerSeries.subst (coefficientBlowupVariables Y hW (fun j ↦ ξ (Sum.inl j)))
          (implicitTransverseCoeff γ (f l))) := by
  sorry

/-- Boundary intersections use total transform and ordinary coefficient pullback.
Both charts are covered by the ordered pair h,j; scalars range over every residue field.
Source: BM 1997, Theorem 7.21, proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG step 13. Substitute W_j=e(c+W'_j), leaving Z fixed. Orders do not fall,
and restriction to pure Z preserves the degree-d_i initial forms. Block triangular
homogeneous division gives (2); Z differentiation preserves (4),(5). Finite jet rank
specialization gives the reverse Hilbert inequality to supported division, hence equality.
The Hilbert criterion for division gives (3). Coefficient extraction commutes with the
substitution in W. This is the total-transform operation specified by the node. -/
theorem coefficient_boundary_chart {L : Type u} [Field L] [CharZero L]
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (pick : Fin n → Fin s) (β : Fin n → Fin n →₀ ℕ)
    (hpick : ∀ j : Fin n, α (pick j) = β j + Finsupp.single j 1)
    (hprefix : ∀ (q : ℕ) (j : Fin n), essential α q j → (α (pick j)).degree ≤ q)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (K : Ideal (MvPowerSeries (Fin m ⊕ Fin n) L))
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hf : formalConditions α pick β Q K f)
    (h j : Fin m) (hne : h ≠ j) (ξ : (Fin m ⊕ Fin n) → L) :
    extendedHilbert
      (coefficientTotalTransform {Sum.inl h, Sum.inl j} (Sum.inl h) ξ K) =
        extendedHilbert K ∧
    formalConditions α pick β Q
      (coefficientTotalTransform {Sum.inl h, Sum.inl j} (Sum.inl h) ξ K)
      (fun l ↦ MvPowerSeries.subst
        (coefficientBlowupVariables {Sum.inl h, Sum.inl j} (Sum.inl h) ξ) (f l)) ∧
    ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
      implicitTransverseCoeff γ (MvPowerSeries.subst
        (coefficientBlowupVariables {Sum.inl h, Sum.inl j} (Sum.inl h) ξ) (f l)) =
      MvPowerSeries.subst (coefficientBlowupVariables {h, j} h (fun z ↦ ξ (Sum.inl z)))
        (implicitTransverseCoeff γ (f l)) := by
  sorry

/-- A free coefficient variable preserves the diagram and five conditions and sums H once.
Source: BM 1997, proof of Theorem 9.4; BMT 6.2
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG step 14. Expand supported quotients in the new variable, coefficientwise.
Homogeneous bases and block Jacobians extend. The complement of the diagram is its
product with N; count bounded-total-degree monomials by their new-variable exponent.
Coefficient extraction gives ordinary pullback. Empty diagrams and zero variables obey
the same count, including at q=0. -/
theorem coefficient_free_variable {L : Type u} [Field L] [CharZero L]
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ)
    (pick : Fin n → Fin s) (β : Fin n → Fin n →₀ ℕ)
    (K : Ideal (MvPowerSeries (Fin m ⊕ Fin n) L))
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hf : formalConditions α pick β Q K f) :
    formalConditions α pick β Q
      (K.map (MvPowerSeries.rename (Sum.map Fin.castSucc id)).toRingHom)
      (fun l ↦ MvPowerSeries.rename (Sum.map Fin.castSucc id) (f l)) ∧
    (∀ q : ℕ, extendedHilbert
      (K.map (MvPowerSeries.rename (Sum.map Fin.castSucc id)).toRingHom) q =
        ∑ r ∈ Finset.range (q + 1), extendedHilbert K r) ∧
    ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
      implicitTransverseCoeff γ (MvPowerSeries.rename (Sum.map Fin.castSucc id) (f l)) =
        MvPowerSeries.rename Fin.castSucc (implicitTransverseCoeff γ (f l)) := by
  sorry

private theorem coefficient_order_map {L : Type u} [Field L]
    {E : Type v} [Field E] (ι : L →+* E) {σ : Type}
    (f : MvPowerSeries σ L) : (MvPowerSeries.map ι f).order = f.order := by
  apply le_antisymm
  · apply MvPowerSeries.le_order
    intro d hd
    apply ι.injective
    simpa using MvPowerSeries.coeff_of_lt_order hd
  · exact MvPowerSeries.le_order_map ι

private theorem coefficient_pderiv_map {L : Type u} [Field L]
    {E : Type v} [Field E] (ι : L →+* E) {σ : Type} (j : σ)
    (f : MvPowerSeries σ L) :
    MvPowerSeries.pderiv E j (MvPowerSeries.map ι f) =
      MvPowerSeries.map ι (MvPowerSeries.pderiv L j f) := by
  ext d
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]

private theorem coefficient_iteratedPartial_map {L : Type u} [Field L]
    {E : Type v} [Field E] (ι : L →+* E) {σ : Type} [Fintype σ]
    (δ : σ →₀ ℕ) (f : MvPowerSeries σ L) :
    iteratedPartial δ (MvPowerSeries.map ι f) =
      MvPowerSeries.map ι (iteratedPartial δ f) := by
  classical
  unfold iteratedPartial
  generalize Finset.univ.toList.flatMap (fun j : σ ↦ List.replicate (δ j) j) = js
  induction js generalizing f with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons, coefficient_pderiv_map]
      exact ih _

private theorem coefficient_transverseIdeal_map {L : Type u} [Field L]
    {E : Type v} [Field E] (ι : L →+* E) {m n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (q : ℕ) :
    (transverseIdeal (m := m) (R := L) α q).map (MvPowerSeries.map ι) ≤
      transverseIdeal (m := m) (R := E) α q := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change MvPowerSeries.map ι
    (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin m ⊕ Fin n) L) ∈
      transverseIdeal (m := m) (R := E) α q
  rw [MvPowerSeries.map_X]
  exact Ideal.subset_span ⟨j, hj, rfl⟩

/-- All formal conditions and jet dimensions commute with arbitrary coefficient field extension.
Together with the universal chart formulas above, this includes non-rational exceptional
points by first extending to their residue fields.
Source: BM 1997, Theorems 7.20--7.21; ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG step 14. At every jet order the division and Jacobian statements are finite
matrix identities. Tensor with the extension field; invertible determinants stay invertible.
The supported formal expansion follows by passage through all finite orders. Taylor
uniqueness identifies the coefficient maps. Finite jet dimensions are unchanged. -/
theorem coefficient_field_extension {L : Type u} [Field L] [CharZero L]
    {E : Type v} [Field E] (ι : L →+* E) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (pick : Fin n → Fin s)
    (β : Fin n → Fin n →₀ ℕ)
    (K : Ideal (MvPowerSeries (Fin m ⊕ Fin n) L))
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hf : formalConditions α pick β Q K f) :
    formalConditions α pick β Q (K.map (MvPowerSeries.map ι))
      (fun l ↦ MvPowerSeries.map ι (f l)) ∧
    extendedHilbert (K.map (MvPowerSeries.map ι)) = extendedHilbert K := by
  classical
  rcases hf with ⟨horder, hdivision, hgen, hblocks, hlater⟩
  obtain ⟨hdivision', hgen'⟩ := formal_division_scalar_extension ι α K f
    (fun l ↦ (horder l).1) (fun l ↦ (horder l).2) hdivision hgen
  refine ⟨?_, funext (formal_jet_length_scalar_extension ι K)⟩
  refine ⟨?_, hdivision', hgen', ?_, ?_⟩
  · intro l
    exact ⟨Ideal.mem_map_of_mem _ (horder l).1,
      (coefficient_order_map ι (f l)).trans (horder l).2⟩
  · intro q hq
    obtain ⟨hmem, hdet⟩ := hblocks q hq
    constructor
    · intro j hj
      rw [coefficient_iteratedPartial_map]
      exact coefficient_transverseIdeal_map ι α q
        (Ideal.mem_map_of_mem _ (hmem j hj))
    · convert hdet.map ι using 1
      rw [RingHom.map_det]
      congr 1
      ext j l
      simp only [coefficient_iteratedPartial_map,
        coefficient_pderiv_map, MvPowerSeries.constantCoeff_map]
      rfl
  · intro q hq l hl δ hδ hs hd
    rw [coefficient_iteratedPartial_map]
    exact coefficient_transverseIdeal_map ι α q
      (Ideal.mem_map_of_mem _ (hlater q hq l hl δ hδ hs hd))

/-- A regular realization of the weighted coefficient transform at an equality point.
The coefficient scheme is the actual strict transform of N on the new étale chart.
The coefficient identities specify exact division by its exceptional equation.
This is conclusion data, not an assumed existence witness.
Source: BM 1997, proof of Theorem 9.4, printed p.278
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
structure RegularCoefficientTransform
    {k : Type u} [Field k] {X M : Scheme.{u}}
    {p : M ⟶ Spec (.of k)} {i : X ⟶ M} {a : X} {m n s Q : ℕ}
    {α : Fin s → Fin n →₀ ℕ} (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (J : D.N.IdealSheafData)
    (x' : (J.map D.j).strictTransform (pullback.snd i D.e)) where
  datum : RegularHilbertCoefficientDatum
    ((J.map D.j).blowupMap ≫ D.e ≫ p)
    (strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
      (J.map D.j).support.compl) x' m n s α Q
  supportMap : datum.N ⟶ (J.map D.j).strictTransform D.j
  supportSquare : IsPullback supportMap datum.j
    (strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl) datum.e
  exceptional : Γ(datum.N, ⊤)
  principal : ((J.map D.j).comap
    (datum.j ≫ datum.e ≫ (J.map D.j).blowupMap)).idealOfOpens ⊤ =
      Ideal.span {exceptional}
  coefficients : ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
    if γ.degree < (α l).degree then
      exceptional ^ ((α l).degree - γ.degree) * datum.coeff l γ =
        (supportMap ≫ strictTransformToSource D.j (J.map D.j).blowupMap
          (J.map D.j).support.compl).appTop (D.coeff l γ)
    else datum.coeff l γ = exceptional ^ (γ.degree - (α l).degree) *
      (supportMap ≫ strictTransformToSource D.j (J.map D.j).blowupMap
        (J.map D.j).support.compl).appTop (D.coeff l γ)

/-- Nonincrease, regular quotients, the exact equality criterion and persistence on regular
coefficient models. The center is a smooth closed subscheme of N contained in its order
locus; its ambient image is blown up with the canonical global construction.
Source: BM 1997, Theorems 7.20, 9.4 and Remark 9.5; ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG steps 2--3 and 7--12,14. Smoothness makes the center reduced. Derivatives
of coefficient orders vanish along it, so coefficients belong to its indicated ideal
powers. Faithful flatness of the residue-field diagonal Taylor maps contracts these
memberships to the regular local rings of N, also at nonclosed points. Principalization
on N' gives unique regular quotients. Apply the explicit formal permissible-chart theorem
after extending to the exceptional point's residue field. It gives nonincrease, excludes
the charts missing N', and identifies equality with the quotient order inequalities.
At equality the five conditions and diagram persist. The implicit Taylor calculus
identifies their coefficients with these regular quotients. The equations and their
invertible Jacobians spread on one common étale neighborhood, giving the displayed
data and its cartesian identification with the actual strict transform of N.
The intrinsic normalized Hilbert function equals the extended Taylor-module function
by the jet-control theorem; no uncorrected local function is used at nonclosed points. -/
theorem coefficient_regular_permissible
    {k : Type u} [Field k] [CharZero k] {X M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (i : X ⟶ M)
    [IsClosedImmersion i] [Smooth p] [LocallyOfFiniteType (i ≫ p)]
    [QuasiCompact (i ≫ p)] (a : X) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (J : D.N.IdealSheafData) [Smooth (J.subschemeι ≫ D.j ≫ D.e ≫ p)]
    (hC : (J.support : Set D.N) ⊆ D.orderLocus) :
    (∀ b' : (J.map D.j).strictTransform D.j,
      ∀ e : ((J.map D.j).strictTransform D.j).presheaf.stalk b',
      HilbertSamuel.stalkIdeal ((J.map D.j).comap
        (strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl ≫
          (J.map D.j).blowupMap)) b' = Ideal.span {e} →
      ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
        ∃! c' : ((J.map D.j).strictTransform D.j).presheaf.stalk b',
          e ^ ((α l).degree - γ.degree) * c' =
            (strictTransformToSource D.j (J.map D.j).blowupMap
              (J.map D.j).support.compl).stalkMap b'
              (D.N.presheaf.germ ⊤
                (strictTransformToSource D.j (J.map D.j).blowupMap
                  (J.map D.j).support.compl b') (by trivial) (D.coeff l γ))) ∧
    ∀ x' : (J.map D.j).strictTransform (pullback.snd i D.e),
      (J.map D.j).blowupMap
        (strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
          (J.map D.j).support.compl x') = D.center →
      HilbertSamuel.le
        (HilbertSamuel.function
          (strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
            (J.map D.j).support.compl ≫ (J.map D.j).blowupMap ≫ D.e ≫ p) x')
        (HilbertSamuel.function (i ≫ p) a) ∧
      (HilbertSamuel.function
          (strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
            (J.map D.j).support.compl ≫ (J.map D.j).blowupMap ≫ D.e ≫ p) x' =
          HilbertSamuel.function (i ≫ p) a ↔
        ∃ b' : (J.map D.j).strictTransform D.j,
          strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl b' =
            strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
              (J.map D.j).support.compl x' ∧
          ∃ e : ((J.map D.j).strictTransform D.j).presheaf.stalk b',
            HilbertSamuel.stalkIdeal ((J.map D.j).comap
              (strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl ≫
                (J.map D.j).blowupMap)) b' = Ideal.span {e} ∧
            ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
              ∃ c' : ((J.map D.j).strictTransform D.j).presheaf.stalk b',
                e ^ ((α l).degree - γ.degree) * c' =
                  (strictTransformToSource D.j (J.map D.j).blowupMap
                    (J.map D.j).support.compl).stalkMap b'
                    (D.N.presheaf.germ ⊤
                      (strictTransformToSource D.j (J.map D.j).blowupMap
                        (J.map D.j).support.compl b') (by trivial) (D.coeff l γ)) ∧
                c' ∈ IsLocalRing.maximalIdeal
                  (((J.map D.j).strictTransform D.j).presheaf.stalk b') ^
                    ((α l).degree - γ.degree)) ∧
      (HilbertSamuel.function
          (strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
            (J.map D.j).support.compl ≫ (J.map D.j).blowupMap ≫ D.e ≫ p) x' =
          HilbertSamuel.function (i ≫ p) a →
        Nonempty (RegularCoefficientTransform D J x')) := by
  sorry

/-- Ordinary regular coefficient pullback on an étale-local model, with r new free variables.
The cartesian square identifies its coefficient scheme with the actual inverse image of N.
Source: BM 1997, Theorem 7.21 and proof of Theorem 9.4; ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
structure RegularCoefficientPullback
    {k : Type u} [Field k] {X M : Scheme.{u}}
    {p : M ⟶ Spec (.of k)} {i : X ⟶ M} {a : X} {m n s Q : ℕ}
    {α : Fin s → Fin n →₀ ℕ} (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    {V : Scheme.{u}} (π : V ⟶ D.U)
    (x' : pullback (C := Scheme.{u}) (pullback.snd i D.e) π) (r : ℕ) where
  datum : RegularHilbertCoefficientDatum (π ≫ D.e ≫ p)
    (pullback.snd (pullback.snd i D.e) π) x' (m + r) n s α Q
  supportMap : datum.N ⟶ D.N
  supportSquare : IsPullback supportMap datum.j D.j (datum.e ≫ π)
  coefficients : ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
    datum.coeff l γ = supportMap.appTop (D.coeff l γ)

/-- The ideal of two coefficient-coordinate hyperplanes in the actual regular chart.
The restricted w coordinates are étale on N, so the intersection is transverse to N.
Source: BM 1997, proof of Theorem 9.4, exceptional-intersection case
(blueprint: lem-trf-formal-coefficient-transform-criterion). -/
def coefficientBoundaryCenter
    {k : Type u} [Field k] {X M : Scheme.{u}}
    {p : M ⟶ Spec (.of k)} {i : X ⟶ M} {a : X} {m n s Q : ℕ}
    {α : Fin s → Fin n →₀ ℕ} (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (h j : Fin m) : D.U.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span
    {D.coord (MvPolynomial.X (Sum.inl h)), D.coord (MvPolynomial.X (Sum.inl j))})

/-- On regular models a boundary-intersection blowup uses the actual total transform,
ordinary coefficient pullback, and retains the level at corresponding closed points.
Source: BM 1997, Theorem 7.21 and proof of Theorem 9.4
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG steps 13--14. Both denominator charts leave Z unchanged. The formal boundary
chart theorem gives all five conditions and equality of the Taylor-module dimensions.
Its coefficient identity is ordinary pullback of the original regular functions. The
implicit coordinate calculus identifies the regular Taylor maps and spreads the equations
and invertible Jacobians on a common étale neighborhood. The jet theorem translates its
dimensions to the normalized function. The cartesian square records total transform. -/
theorem coefficient_regular_boundary
    {k : Type u} [Field k] [CharZero k] {X M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (i : X ⟶ M)
    [IsClosedImmersion i] [Smooth p] [LocallyOfFiniteType (i ≫ p)]
    [QuasiCompact (i ≫ p)] (a : X) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (h j : Fin m) (hne : h ≠ j) (ha : IsClosed ({a} : Set X))
    (x' : pullback (C := Scheme.{u}) (pullback.snd i D.e)
      (coefficientBoundaryCenter D h j).blowupMap)
    (hx' : IsClosed ({x'} : Set
      (pullback (C := Scheme.{u}) (pullback.snd i D.e)
        (coefficientBoundaryCenter D h j).blowupMap)))
    (hover : (coefficientBoundaryCenter D h j).blowupMap
      (pullback.snd (pullback.snd i D.e) (coefficientBoundaryCenter D h j).blowupMap x') =
        D.center) :
    HilbertSamuel.function
      (pullback.snd (pullback.snd i D.e) (coefficientBoundaryCenter D h j).blowupMap ≫
        (coefficientBoundaryCenter D h j).blowupMap ≫ D.e ≫ p) x' =
      HilbertSamuel.function (i ≫ p) a ∧
    Nonempty (RegularCoefficientPullback D (coefficientBoundaryCenter D h j).blowupMap
      x' 0) := by
  sorry

/-- The regular affine-line operation pulls back coefficients and sums the extended function.
Source: BM 1997, proof of Theorem 9.4; BMT 6.2
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG step 14. On the relative line the inverse image of N is its relative line.
Expand all supported identities in its new coordinate; the formal free-variable theorem
sums the bounded-degree monomial count once. This also works over the residue field of
a nonclosed lift, with the diagonal Taylor convention. The original regular coefficients
pull back through the displayed cartesian square. Shrink étale locally for the common
regular model and its Hilbert bound. -/
theorem coefficient_regular_line
    {k : Type u} [Field k] [CharZero k] {X M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (i : X ⟶ M)
    [IsClosedImmersion i] [Smooth p] [LocallyOfFiniteType (i ≫ p)]
    [QuasiCompact (i ≫ p)] (a : X) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (x' : pullback (C := Scheme.{u}) (pullback.snd i D.e)
      (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U))
    (hover : (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U)
      (pullback.snd (pullback.snd i D.e) (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U) x') =
        D.center) :
    HilbertSamuel.function
      (pullback.snd (pullback.snd i D.e) (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U) ≫
        (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U) ≫ D.e ≫ p) x' =
      HilbertSamuel.summation (HilbertSamuel.function (i ≫ p) a) ∧
    Nonempty (RegularCoefficientPullback D
      (AffineSpace (ULift.{u} (Fin 1)) D.U ↘ D.U) x' 1) := by
  sorry

/-- Every pointed étale localization retains the formulas and the extended function,
including arbitrary lifts with a residue field extension.
Source: BM 1997, Remark 9.5; ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-formal-coefficient-transform-criterion).

Proof: DAG step 14. Étale Taylor uniqueness identifies the old and pulled-back finite
Taylor modules after the residue field extension. Their dimensions agree, and their
coefficient identities are the pullbacks of the same regular functions. Pull back the
coefficient scheme cartesianly and retain the five identities and their invertible
Jacobians; restrict to a common affine étale neighborhood. -/
theorem coefficient_regular_etale
    {k : Type u} [Field k] [CharZero k] {X M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (i : X ⟶ M)
    [IsClosedImmersion i] [Smooth p] [LocallyOfFiniteType (i ≫ p)]
    [QuasiCompact (i ≫ p)] (a : X) {m n s Q : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    {V : Scheme.{u}} (g : V ⟶ D.U) [Etale g]
    (x' : pullback (C := Scheme.{u}) (pullback.snd i D.e) g)
    (hover : g (pullback.snd (pullback.snd i D.e) g x') = D.center) :
    HilbertSamuel.function
      (pullback.snd (pullback.snd i D.e) g ≫ g ≫ D.e ≫ p) x' =
        HilbertSamuel.function (i ≫ p) a ∧
    Nonempty (RegularCoefficientPullback D g x' 0) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
