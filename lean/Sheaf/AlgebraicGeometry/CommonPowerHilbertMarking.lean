/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion
public import Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Field.ULift

import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-! # Common-power Hilbert coefficient markings

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; Bierstone--Milman (1997),
Theorems 7.20, 9.4, 9.6; BMT 6.2
(blueprint: lem-trf-common-power-hilbert-marking).

The generated ideal is constructed from the supplied coefficients. Regular division
is expressed by multiplication identities on every affine open of the actual strict
transform, including opens missing the exceptional divisor. The equality assertion is
local about the distinguished point, with one further ambient restriction allowed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertCoefficient

/-- The actual common-power ideal associated to a coefficient family. The empty family
has empty generating set, hence gives the zero ideal, independently of the mark.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorem 9.4
(blueprint: lem-trf-common-power-hilbert-marking). -/
def commonPowerIdeal {N : Scheme.{u}} {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤))
    (b : ℕ) : N.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span
    {f | ∃ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree ∧
      f = c l γ ^ (b / ((α l).degree - γ.degree))})

/-- The same common-power expression in an arbitrary ring, used for chart sections.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorem 9.4
(blueprint: lem-trf-common-power-hilbert-marking). -/
def commonPowerRingIdeal {R : Type u} [CommRing R] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → R) (b : ℕ) : Ideal R :=
  Ideal.span {f | ∃ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree ∧
    f = c l γ ^ (b / ((α l).degree - γ.degree))}

private theorem ideal_coherent_of_smooth {N : Scheme.{u}}
    (p : N ⟶ Spec (.of (ULift.{u} ℚ))) [Smooth p] (I : N.IdealSheafData) :
    RingedSpace.IsCoherent N.toRingedSpace I.toModules := by
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian p
  have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := N.ringCatSheaf)
  have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion I.subschemeι _
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType N I.toModules).mpr
    ⟨Scheme.Modules.isQuasicoherent_kernel I.toPushforwardSubscheme,
      I.isFiniteType_toModules_sheaf I.ofFiniteType_of_isLocallyNoetherian⟩

private theorem stalk_ofIdealTop {N : Scheme.{u}} [IsAffine N]
    (I : Ideal Γ(N, ⊤)) (x : N) :
    HilbertSamuel.stalkIdeal (Scheme.IdealSheafData.ofIdealTop I) x =
      I.map (N.presheaf.germ ⊤ x (by trivial)).hom := by
  apply le_antisymm
  · refine iSup_le fun U ↦ iSup_le fun hx ↦ ?_
    rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, ← CommRingCat.hom_comp,
      N.presheaf.germ_res]
  · apply le_iSup_of_le (⟨⊤, isAffineOpen_top N⟩ : N.affineOpens)
    apply le_iSup_of_le (show x ∈ (⊤ : N.Opens) from trivial)
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map,
      ← CommRingCat.hom_comp, N.presheaf.germ_res, le_refl]

private theorem nat_le_order_iff {N : Scheme.{u}} (I : N.IdealSheafData)
    (x : N) (b : ℕ) :
    (b : ℕ∞) ≤ HilbertSamuel.order I x ↔
      HilbertSamuel.stalkIdeal I x ≤ IsLocalRing.maximalIdeal (N.presheaf.stalk x) ^ b := by
  constructor
  · cases b with
    | zero => simp
    | succ b =>
      intro hb
      by_contra hn
      have hbound : HilbertSamuel.order I x ≤ (b : ℕ∞) := by
        refine iSup_le fun q ↦ iSup_le fun hq ↦ ?_
        have hqb : q ≤ b := by
          by_contra h
          exact hn (hq.trans (Ideal.pow_le_pow_right (by omega)))
        exact_mod_cast hqb
      have := hb.trans hbound
      exact (Nat.not_succ_le_self b) (by exact_mod_cast this)
  · intro h
    exact le_iSup_of_le b (le_iSup_of_le h le_rfl)

-- Minimal parameters are regular, so the tangent cone is a polynomial ring over a field.
private theorem regular_graded_domain {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsDomain (Ideal.associatedGraded (IsLocalRing.maximalIdeal R)) := by
  classical
  obtain ⟨t, htcard, htspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let f : Fin t.card → R := fun j ↦ t.toList.get (Fin.cast (by simp) j)
  have hfrange : Set.range f = (t : Set R) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨j, rfl⟩
      exact Finset.mem_toList.mp (List.get_mem _ _)
    · intro hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hx)
      refine ⟨Fin.cast (by simp) j, ?_⟩
      exact (congrArg t.toList.get (Fin.ext rfl)).trans hj
  have hspan : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal R := by
    rw [hfrange]
    exact htspan
  have hreg : RingTheory.Sequence.IsRegular R (List.ofFn f) := by
    apply (IsRegularLocalRing.isRegular_and_quotients_of_generators
      R t.card ?_ (List.ofFn f) ?_).1
    · rw [htcard]
      exact IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    · refine ⟨?_, ?_⟩
      · simpa only [List.mem_ofFn', Set.ofPred_mem_eq] using hspan
      · simpa only [List.length_ofFn] using
          (show (t.card : WithBot ℕ∞) = ringKrullDim R by
            rw [htcard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal)
  have : (Ideal.span (Set.range f)).IsMaximal :=
    hspan ▸ IsLocalRing.maximalIdeal.isMaximal R
  let e := RingEquiv.ofBijective (Ideal.regularSequenceGradedPolynomialMap f).toRingHom
    (Ideal.regularSequence_gradedPolynomial f hreg).1
  have hd : IsDomain (Ideal.associatedGraded (Ideal.span (Set.range f))) :=
    e.symm.injective.isDomain e.symm
  rwa [hspan] at hd

private theorem graded_class_pow {R : Type u} [CommRing R] (J : Ideal R)
    (x : R) (d : ℕ) (hx : x ∈ J ^ d) (q : ℕ) :
    (DirectSum.of (Ideal.associatedGradedPiece J) d
      (Submodule.Quotient.mk (⟨x, hx⟩ : (J ^ d : Ideal R)))) ^ q =
      DirectSum.of (Ideal.associatedGradedPiece J) (d * q)
        (Submodule.Quotient.mk
          (⟨x ^ q, by simpa only [pow_mul] using Ideal.pow_mem_pow hx q⟩ :
            (J ^ (d * q) : Ideal R))) := by
  induction q with
  | zero => simpa using Ideal.associatedGraded_one J
  | succ q ih =>
    rw [pow_succ, ih, Ideal.associatedGraded_mul]
    simp only [Nat.mul_succ, pow_succ]

-- A least nonzero initial form stays nonzero after every positive power.
private theorem regular_power_mem {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (x : R) (d q : ℕ) (hq : 0 < q) :
    x ^ q ∈ IsLocalRing.maximalIdeal R ^ (d * q) ↔
      x ∈ IsLocalRing.maximalIdeal R ^ d := by
  classical
  have := regular_graded_domain (R := R)
  let J := IsLocalRing.maximalIdeal R
  constructor
  · intro hxq
    by_contra hn
    cases d with
    | zero => exact hn (by simp)
    | succ d =>
      let hfail : ∃ r : ℕ, x ∉ J ^ (r + 1) := ⟨d, hn⟩
      let r := Nat.find hfail
      have hr : x ∉ J ^ (r + 1) := Nat.find_spec hfail
      have hrd : r ≤ d := Nat.find_min' hfail hn
      have hx : x ∈ J ^ r := by
        cases heq : r with
        | zero => simp
        | succ j =>
          by_contra h
          exact Nat.find_min hfail (show j < Nat.find hfail from by change j < r; omega) h
      let z : Ideal.associatedGraded J :=
        DirectSum.of (Ideal.associatedGradedPiece J) r
          (Submodule.Quotient.mk (⟨x, hx⟩ : (J ^ r : Ideal R)))
      have hz : z ≠ 0 := by
        intro h
        have hclass := (DirectSum.of_injective (β := Ideal.associatedGradedPiece J) r)
          (h.trans (map_zero _).symm)
        have hmem : (⟨x, hx⟩ : (J ^ r : Ideal R)) ∈
            Submodule.comap (J ^ r : Submodule R R).subtype
              (J ^ (r + 1) : Submodule R R) :=
          (Submodule.Quotient.mk_eq_zero _).mp hclass
        exact hr hmem
      have hxq' : x ^ q ∈ J ^ (r * q + 1) :=
        Ideal.pow_le_pow_right (by nlinarith) hxq
      have hzq : z ^ q = 0 := by
        rw [graded_class_pow J x r hx q]
        rw [(Submodule.Quotient.mk_eq_zero
          (Submodule.comap (J ^ (r * q) : Submodule R R).subtype
            (J ^ (r * q + 1) : Submodule R R))).mpr hxq', map_zero]
      exact pow_ne_zero q hz hzq
  · intro hx
    simpa only [pow_mul] using Ideal.pow_mem_pow hx q

private theorem commonPower_order {N : Scheme.{u}} [IsAffine N] [IsRegular N]
    {n s : ℕ} (α : Fin s → Fin n →₀ ℕ)
    (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)) (b : ℕ) (hb : 0 < b)
    (hdiv : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      (α l).degree - γ.degree ∣ b) (x : N) :
    (b : ℕ∞) ≤ HilbertSamuel.order (commonPowerIdeal α c b) x ↔
      ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
        N.presheaf.germ ⊤ x (by trivial) (c l γ) ∈
          IsLocalRing.maximalIdeal (N.presheaf.stalk x) ^ ((α l).degree - γ.degree) := by
  rw [nat_le_order_iff, commonPowerIdeal, stalk_ofIdealTop, Ideal.map_span,
    Ideal.span_le]
  constructor
  · intro h l γ hγ
    have hgen := h ⟨c l γ ^ (b / ((α l).degree - γ.degree)), ⟨l, γ, hγ, rfl⟩, rfl⟩
    have hmul := Nat.mul_div_cancel' (hdiv l γ hγ)
    have hpos : 0 < b / ((α l).degree - γ.degree) :=
      Nat.div_pos (Nat.le_of_dvd hb (hdiv l γ hγ)) (Nat.sub_pos_of_lt hγ)
    apply (regular_power_mem _ _ _ hpos).mp
    simpa only [hmul, map_pow, CommRingCat.Hom.hom, SetLike.mem_coe] using hgen
  · rintro h _ ⟨f, ⟨l, γ, hγ, rfl⟩, rfl⟩
    have hp := Ideal.pow_mem_pow (h l γ hγ) (b / ((α l).degree - γ.degree))
    simpa only [map_pow, ← pow_mul, Nat.mul_div_cancel' (hdiv l γ hγ),
      CommRingCat.Hom.hom, SetLike.mem_coe] using hp

/-- Coherence, the coefficient order criterion, and the Hilbert equality germ.
For an empty vertex list the convention is `b = 1`; its ideal is zero and its
cosupport is all of N. The displayed image equality is inside the common étale chart.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorems 7.20, 9.4, 9.6
(blueprint: lem-trf-common-power-hilbert-marking).

Proof (node steps 1--3): The finitely many low coefficients generate the displayed
ideal; their restrictions localize, so it is quasi-coherent and finite type.
Smoothness gives local Noetherianity by lem-weil-pbc-smooth-scheme-over-field-regular,
and pqf-lem-coherent-ft-locnoeth gives coherence, including the zero ideal.
A minimal generating list of the maximal ideal of a regular local ring is a regular
sequence. Its associated graded ring is a polynomial ring over the residue field,
hence a domain. Taking powers of a nonzero initial form proves
ord(c^(b/m)) >= b iff ord(c) >= m. Containment in a maximal-ideal power is tested
on the generators; for an empty family both tests hold everywhere.
Apply lem-trf-formal-coefficient-transform-criterion with the supplied five conditions
and the jet bound. Its equality is a germ assertion, so shrink once about the center.
The criterion already states its conclusion using HilbertSamuel.function, including
at nonclosed points; no separate jet comparison is needed here.
-/
theorem commonPowerHilbertMarking
    {X M : Scheme.{u}} (p : M ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ M)
    [IsClosedImmersion i] [IsReduced X] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (a : X) (hH : ∀ x : X,
      HilbertSamuel.le (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) x)
        (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a))
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (b : ℕ) (hb : 0 < b) (hempty : s = 0 → b = 1)
    (hdiv : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      (α l).degree - γ.degree ∣ b) :
    RingedSpace.IsCoherent D.N.toRingedSpace (commonPowerIdeal α D.coeff b).toModules ∧
    {x : D.N | (b : ℕ∞) ≤ HilbertSamuel.order (commonPowerIdeal α D.coeff b) x} =
      D.orderLocus ∧
    (s = 0 → commonPowerIdeal α D.coeff b = 0) ∧
    ∃ V : D.U.Opens, D.center ∈ V ∧ ∀ y : D.U, y ∈ V →
      ((∃ x : pullback (C := Scheme.{u}) i D.e, pullback.snd i D.e x = y ∧
          HilbertSamuel.function (k := ULift.{u} ℚ) (pullback.snd i D.e ≫ D.e ≫ p) x =
            HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a) ↔
        ∃ z : D.N, D.j z = y ∧
          (b : ℕ∞) ≤ HilbertSamuel.order (commonPowerIdeal α D.coeff b) z) := by
  have _ := hH a
  have : IsAffine D.N := D.affineN
  have : Smooth (D.j ≫ D.e ≫ p) := D.smoothN
  have : IsRegular D.N := IsRegular.of_smooth (D.j ≫ D.e ≫ p)
  have horder (x : D.N) := commonPower_order α D.coeff b hb hdiv x
  refine ⟨ideal_coherent_of_smooth (D.j ≫ D.e ≫ p) _, ?_, ?_, ?_⟩
  · exact Set.ext fun x ↦ horder x
  · intro hs
    subst s
    apply Scheme.IdealSheafData.ext
    funext U
    simp [commonPowerIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
  · have : CharZero (ULift.{u} ℚ) :=
      (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero
    obtain ⟨V, hV, hEq⟩ := coefficient_equality_germ p i a α hα hQ D
    refine ⟨V, hV, fun y hy ↦ (hEq y hy).trans ?_⟩
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, rfl, (horder z).mpr hz⟩
    · rintro ⟨z, rfl, hz⟩
      exact ⟨z, (horder z).mp hz, rfl⟩

/-- Every exceptional chart has regular coefficient quotients and their common powers
are exactly the controlled ideal. The multiplication identity expresses `e^(-b) I_b`
without fractions, while the colon identity specifies exact division as an ideal.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorem 7.20
(blueprint: lem-trf-common-power-hilbert-marking).

Proof (node steps 4--5): Apply lem-trf-marked-controlled-blowup-charts to each principal
coefficient ideal with mark d_i-|gamma|, using the order locus condition. It gives
membership in the corresponding center power and regular quotients on N'. Apply the
same theorem to I_b with mark b. On a chart, raising e^m c'=sigma*c to b/m gives
 e^b (c')^(b/m)=sigma*(c^(b/m)), since m divides b. Pullback of a generated ideal is
generated by the pulled-back functions; sum these identities. A change of exceptional
equation by a unit changes the generators by unit powers and preserves the ideal.
Empty lists yield zero on both sides. Exact division agrees with the controlled ideal
quotient, using the intrinsic-blowup identification of the cited chart theorem.
-/
theorem commonPowerHilbertMarking_charts
    {X M : Scheme.{u}} (p : M ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ M)
    [IsClosedImmersion i] [IsReduced X] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (a : X) {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (b : ℕ) (hb : 0 < b) (hempty : s = 0 → b = 1)
    (hdiv : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      (α l).degree - γ.degree ∣ b)
    (J : D.N.IdealSheafData) [Smooth (J.subschemeι ≫ D.j ≫ D.e ≫ p)]
    (hC : (J.support : Set D.N) ⊆ D.orderLocus)
    (E : List D.U.IdealSheafData)
    (hflag : HasEtaleCoordinateFlag (D.e ≫ p) D.j.ker (J.map D.j) E) :
    ∀ (V : ((J.map D.j).strictTransform D.j).affineOpens)
      (e : Γ((J.map D.j).strictTransform D.j, V.1)),
      ((J.map D.j).comap
        (strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl ≫
          (J.map D.j).blowupMap)).ideal V = Ideal.span {e} →
      ∃ c' : Fin s → (Fin n →₀ ℕ) → Γ((J.map D.j).strictTransform D.j, V.1),
        (∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
          e ^ ((α l).degree - γ.degree) * c' l γ =
            (strictTransformToSource D.j (J.map D.j).blowupMap
              (J.map D.j).support.compl).appLE ⊤ V.1 (by intro x hx; trivial)
                (D.coeff l γ)) ∧
        commonPowerRingIdeal α c' b =
          (controlledTransformIdeal
            (strictTransformToSource D.j (J.map D.j).blowupMap (J.map D.j).support.compl)
            J (commonPowerIdeal α D.coeff b) b).ideal V ∧
        commonPowerRingIdeal α c' b * Ideal.span {e ^ b} =
          ((commonPowerIdeal α D.coeff b).comap
            (strictTransformToSource D.j (J.map D.j).blowupMap
              (J.map D.j).support.compl)).ideal V := by
  sorry

/-- The actual strict transform of the embedded scheme in the supplied coefficient chart.
Source: BM (1997), Theorem 9.4
(blueprint: lem-trf-common-power-hilbert-marking). -/
abbrev coefficientModifiedX
    {X M : Scheme.{u}} {p : M ⟶ Spec (.of (ULift.{u} ℚ))} {i : X ⟶ M}
    {a : X} {m n s Q : ℕ} {α : Fin s → Fin n →₀ ℕ}
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (J : D.N.IdealSheafData) :=
  (J.map D.j).strictTransform (pullback.snd i D.e)

/-- Projection of the modified embedded scheme to the original common chart.
Source: BM (1997), Theorem 9.4
(blueprint: lem-trf-common-power-hilbert-marking). -/
abbrev coefficientModifiedMap
    {X M : Scheme.{u}} {p : M ⟶ Spec (.of (ULift.{u} ℚ))} {i : X ⟶ M}
    {a : X} {m n s Q : ℕ} {α : Fin s → Fin n →₀ ℕ}
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (J : D.N.IdealSheafData) :=
  strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
    (J.map D.j).support.compl ≫ (J.map D.j).blowupMap

/-- Projection of the actual modified coefficient scheme to the original one.
Source: BM (1997), Theorem 9.4
(blueprint: lem-trf-common-power-hilbert-marking). -/
abbrev coefficientModifiedSupportMap
    {X M : Scheme.{u}} {p : M ⟶ Spec (.of (ULift.{u} ℚ))} {i : X ⟶ M}
    {a : X} {m n s Q : ℕ} {α : Fin s → Fin n →₀ ℕ}
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (J : D.N.IdealSheafData) :=
  strictTransformToSource D.j (J.map D.j).blowupMap (J.map D.j).support.compl

/-- After a common shrinking, nonincrease above every center point, exact equality on
N', and persistence of the diagram and all five conditions. The existential point of N'
excludes equality on charts missing N'. Outside the center all functions and ideals
identify through the canonical complement isomorphisms.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorems 7.20, 9.4, 9.6
(blueprint: lem-trf-common-power-hilbert-marking).

Proof (node steps 6--7): At each point of C apply the formal coefficient transform
criterion to the supplied five conditions and its coordinate center. This gives
nonincrease, equality exactly at the coefficient inequalities on N', and persistence
of the diagram and all five conditions at equality. The jet-control theorem identifies
the extended formal dimensions with H_X, including nonclosed points. Apply the product
and sum order calculation of step 2 on smooth N' to the regular coefficients from
step 4: their inequalities are the cosupport of the common-power controlled ideal
from step 5. The formal criterion excludes equality in charts missing N'. Over the
complement, thm-nagata-global-blowup-complement and
lemma-nagata-strict-transform-over-complement give the canonical scheme identifications.
The exceptional ideal is the unit ideal, so the controlled ideal is the original one.
Isomorphic local rings and residue fields give the same normalized Hilbert sequence.
-/
theorem commonPowerHilbertMarking_transform
    {X M : Scheme.{u}} (p : M ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ M)
    [IsClosedImmersion i] [IsReduced X] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (a : X) (hH : ∀ x : X,
      HilbertSamuel.le (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) x)
        (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a))
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (D : RegularHilbertCoefficientDatum (k := ULift.{u} ℚ) p i a m n s α Q)
    (b : ℕ) (hb : 0 < b) (hempty : s = 0 → b = 1)
    (hdiv : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      (α l).degree - γ.degree ∣ b) :
    ∃ V : D.U.Opens, D.center ∈ V ∧
      ∀ (J : D.N.IdealSheafData), Smooth (J.subschemeι ≫ D.j ≫ D.e ≫ p) →
      (J.support : Set D.N) ⊆ D.orderLocus →
      (J.support : Set D.N) ⊆ D.j ⁻¹' (V : Set D.U) →
      ∀ E : List D.U.IdealSheafData,
      HasEtaleCoordinateFlag (D.e ≫ p) D.j.ker (J.map D.j) E →
      (∀ x' : coefficientModifiedX D J,
        coefficientModifiedMap D J x' ∈ (J.map D.j).support →
        HilbertSamuel.le
          (HilbertSamuel.function (k := ULift.{u} ℚ) (coefficientModifiedMap D J ≫ D.e ≫ p) x')
          (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a) ∧
        (HilbertSamuel.function (k := ULift.{u} ℚ) (coefficientModifiedMap D J ≫ D.e ≫ p) x' =
            HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a ↔
          ∃ z : (J.map D.j).strictTransform D.j,
            strictTransformMap D.j (J.map D.j).blowupMap (J.map D.j).support.compl z =
              strictTransformMap (pullback.snd i D.e) (J.map D.j).blowupMap
                (J.map D.j).support.compl x' ∧
            (b : ℕ∞) ≤ HilbertSamuel.order
              (controlledTransformIdeal (coefficientModifiedSupportMap D J)
                J (commonPowerIdeal α D.coeff b) b) z) ∧
        (HilbertSamuel.function (k := ULift.{u} ℚ) (coefficientModifiedMap D J ≫ D.e ≫ p) x' =
            HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) a →
          Nonempty (RegularCoefficientTransform D J x'))) ∧
      IsIso ((J.map D.j).blowupMap ∣_ (J.map D.j).support.compl) ∧
      IsIso (coefficientModifiedSupportMap D J ∣_ J.support.compl) ∧
      IsIso (strictTransformToSource (pullback.snd i D.e) (J.map D.j).blowupMap
        (J.map D.j).support.compl ∣_
          ((J.map D.j).comap (pullback.snd i D.e)).support.compl) ∧
      (controlledTransformIdeal (coefficientModifiedSupportMap D J)
          J (commonPowerIdeal α D.coeff b) b).comap
            ((coefficientModifiedSupportMap D J ⁻¹ᵁ J.support.compl).ι) =
        ((commonPowerIdeal α D.coeff b).comap (coefficientModifiedSupportMap D J)).comap
          ((coefficientModifiedSupportMap D J ⁻¹ᵁ J.support.compl).ι) ∧
      (∀ x' : coefficientModifiedX D J,
        coefficientModifiedMap D J x' ∉ (J.map D.j).support →
        HilbertSamuel.function (k := ULift.{u} ℚ) (coefficientModifiedMap D J ≫ D.e ≫ p) x' =
          HilbertSamuel.function (k := ULift.{u} ℚ) (pullback.snd i D.e ≫ D.e ≫ p)
            (strictTransformToSource (pullback.snd i D.e) (J.map D.j).blowupMap
              (J.map D.j).support.compl x')) := by
  sorry

/-- A smooth center on which the intrinsic Hilbert--Samuel function is locally constant
has a pointwise nonincreasing ambient blowup, even across components with different levels.
Source: ILO VIII 2.3.11--2.3.13; BM (1997), Theorems 9.4, 9.6; BMT 6.2
(blueprint: lem-trf-common-power-hilbert-marking).

Proof (node step 8): At each center point shrink until H is constant on the center.
lem-trf-regular-hilbert-coefficient-data gives data for sufficiently large Q and H bounded
by its value there. The initial equality criterion places the center in N set-theoretically;
smoothness makes it reduced, hence it factors through closed N. Apply
lem-pur-smooth-pair-local-coordinates to N in the ambient and then to C in N. On an affine
restriction lift the coordinates of N and append its regular equations. The square is
cartesian; lem-pur-etale-near-regular-coordinate-fibre makes this lifted map étale near
the point, giving simultaneous flag coordinates with empty boundary. The chart and
transform clauses give nonincrease above that point. Away from the center the canonical
complement isomorphisms give equality. This is pointwise and allows different locally
constant levels on different components of C.
-/
theorem hilbertSamuel_le_of_smooth_locally_constant_center
    {X M : Scheme.{u}} (p : M ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ M)
    [IsClosedImmersion i] [IsReduced X] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (J : X.IdealSheafData) [Smooth (J.subschemeι ≫ i ≫ p)]
    (hH : IsLocallyConstant (fun x : J.subscheme ↦
      HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p) (J.subschemeι x))) :
    ∀ x' : (J.map i).strictTransform i,
      HilbertSamuel.le
        (HilbertSamuel.function (k := ULift.{u} ℚ)
          (strictTransformToSource i (J.map i).blowupMap (J.map i).support.compl ≫ i ≫ p)
          x')
        (HilbertSamuel.function (k := ULift.{u} ℚ) (i ≫ p)
          (strictTransformToSource i (J.map i).blowupMap (J.map i).support.compl x')) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
