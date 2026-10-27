/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolynomialLogChartBasic
import Sheaf.AlgebraicGeometry.PolynomialLogChartStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Polynomial logarithmic charts

Source: ILO, Travaux de Gabber, Exposé VI 1.1--1.2 and 1.8--1.9, pp.69--71;
Stacks Project, Tags 031E and 00ON
(blueprint: lem-trf-polynomial-log-chart-regularity).

## Main declarations

* `PolynomialLogChart.structuralMap`: the specified product chart map.
* `PolynomialLogChart.nonunitIdeal`: transport of the existing nonunit ideal.
* `PolynomialLogChart.characteristicChart`: the canonical chart image in the characteristic.
* `PolynomialLogChart.coordinate` and `vanishingCoordinates`: the actual variables and set `K`.
* `polynomial_log_chart_regularity`: fs log regularity and all the local formulas.

The free additive monoid is written multiplicatively with `Multiplicative`.
All stalk ideals are transported along the canonical affine-colimit comparison.
The characteristic isomorphism is specified on every chart element, including
coordinates that become units. No associated log structure is chosen from existence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The log-regularity conjunction transports along the canonical strict-local comparison.
Source: ILO VI 1.2 (blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem strict_log_regular_iff
    {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (IsRegularRing (strictLocalRing X x ⧸ M.nonunitIdeal x) ∧
      ringKrullDim (strictLocalRing X x) =
        ringKrullDim (strictLocalRing X x ⧸ M.nonunitIdeal x) +
          (M.characteristicRank x : WithBot ℕ∞)) ↔
    (IsRegularRing (Scheme.strictHenselizationRing x ⧸ PolynomialLogChart.nonunitIdeal M x) ∧
      ringKrullDim (Scheme.strictHenselizationRing x) =
        ringKrullDim (Scheme.strictHenselizationRing x ⧸ PolynomialLogChart.nonunitIdeal M x) +
          (M.characteristicRank x : WithBot ℕ∞)) := by
  let e := (strictLocalRingStrictHenselizationIso X x).commRingCatIsoToRingEquiv
  let q := Ideal.quotientEquiv (M.nonunitIdeal x)
    (PolynomialLogChart.nonunitIdeal M x) e rfl
  have hd := ringKrullDim_eq_of_ringEquiv e
  have hq := ringKrullDim_eq_of_ringEquiv q
  constructor
  · rintro ⟨hr, hdim⟩
    let := hr
    exact ⟨IsRegularRing.of_ringEquiv q, by rwa [← hd, ← hq]⟩
  · rintro ⟨hr, hdim⟩
    let := hr
    exact ⟨IsRegularRing.of_ringEquiv q.symm, by rwa [hd, hq]⟩

/-- The flat height formula at the maximal ideals of a local map.
Source: Stacks Tag 00ON (blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem local_flat_dimension
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    ringKrullDim B = ringKrullDim A +
      ringKrullDim (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hφ
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap φ).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  have : Nontrivial (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top φ))
  have := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A)))
    Ideal.Quotient.mk_surjective
  have hm := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)) Ideal.Quotient.mk_surjective
  rw [show algebraMap A B = φ from rfl, hm] at h
  simpa only [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, WithBot.coe_add]
    using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) h

/-- The closed fibre of a quotient local map is the quotient by the sum of ideals.
Source: Stacks Tag 00ON and the third isomorphism theorem
(blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem quotient_fibre_equiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (I : Ideal A) (J : Ideal B) (hIJ : I ≤ Ideal.comap φ J)
    [IsLocalRing (A ⧸ I)] :
    Nonempty (((B ⧸ J) ⧸ Ideal.map (Ideal.quotientMap J φ hIJ)
      (IsLocalRing.maximalIdeal (A ⧸ I))) ≃+*
      (B ⧸ (J ⊔ Ideal.map φ (IsLocalRing.maximalIdeal A)))) := by
  let ψ := Ideal.quotientMap J φ hIJ
  have hm := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have he : Ideal.map ψ (IsLocalRing.maximalIdeal (A ⧸ I)) =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.map φ (IsLocalRing.maximalIdeal A)) := by
    rw [← hm, Ideal.map_map, Ideal.map_map]
    congr 1
  exact ⟨(Ideal.quotEquivOfEq he).trans (DoubleQuot.quotQuotEquivQuotSup J
    (Ideal.map φ (IsLocalRing.maximalIdeal A)))⟩

/-- Transport quotient-map flatness through an equality of quotient ideals.
Source: equality elimination (blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem quotientMap_flat_congr
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J L : Ideal B) (h : J = L)
    (hIJ : I ≤ Ideal.comap φ J) (hIL : I ≤ Ideal.comap φ L)
    (hf : (Ideal.quotientMap J φ hIJ).Flat) :
    (Ideal.quotientMap L φ hIL).Flat := by
  subst L
  exact hf

/-- Combine flat regularity with the two flat dimension formulas, without subtraction.
Source: Stacks Tags 031E, 00ON, 0AFS; ILO VI 1.2
(blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem stratum_regular_dimension
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat)
    (I : Ideal A) (J : Ideal B) (hIJ : I ≤ Ideal.comap φ J)
    [IsLocalRing (A ⧸ I)] [IsLocalRing (B ⧸ J)]
    [IsRegularRing (A ⧸ I)] [IsRegularRing D]
    (hψ : (Ideal.quotientMap J φ hIJ).Flat)
    [IsLocalHom (Ideal.quotientMap J φ hIJ)]
    (e : (B ⧸ (J ⊔ Ideal.map φ (IsLocalRing.maximalIdeal A))) ≃+* D)
    (ρ : ℕ∞) (k : ℕ)
    (hA : ringKrullDim A = ringKrullDim (A ⧸ I) + (ρ : WithBot ℕ∞))
    (hF : ringKrullDim (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) =
      ringKrullDim D + k) :
    IsRegularRing (B ⧸ J) ∧
      ringKrullDim B = ringKrullDim (B ⧸ J) + (ρ : WithBot ℕ∞) + k := by
  let ψ := Ideal.quotientMap J φ hIJ
  let E := (quotient_fibre_equiv φ I J hIJ).some.trans e
  have hclosed : IsRegularRing ((B ⧸ J) ⧸
      Ideal.map ψ (IsLocalRing.maximalIdeal (A ⧸ I))) :=
    IsRegularRing.of_ringEquiv E.symm
  have : Nontrivial ((B ⧸ J) ⧸
      Ideal.map ψ (IsLocalRing.maximalIdeal (A ⧸ I))) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top ψ))
  have := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.map ψ (IsLocalRing.maximalIdeal (A ⧸ I))))
    Ideal.Quotient.mk_surjective
  have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing (A ⧸ I)
  have hfibre := IsRegularLocalRing.of_isRegularRing_of_isLocalRing
    ((B ⧸ J) ⧸ Ideal.map ψ (IsLocalRing.maximalIdeal (A ⧸ I)))
  have := IsRegularLocalRing.of_flat_of_regular_closedFiber ψ hψ hfibre
  have hr := (IsRegularLocalRing.localization_at_prime_and_isRegularRing
    (IsLocalRing.maximalIdeal (B ⧸ J))).2
  refine ⟨hr, ?_⟩
  have hB := local_flat_dimension φ hφ
  have hBJ := local_flat_dimension ψ hψ
  rw [ringKrullDim_eq_of_ringEquiv E] at hBJ
  calc
    ringKrullDim B = (ringKrullDim (A ⧸ I) + (ρ : WithBot ℕ∞)) +
        (ringKrullDim D + k) := by rw [hB, hA, hF]
    _ = (ringKrullDim (A ⧸ I) + ringKrullDim D) + (ρ : WithBot ℕ∞) + k := by
      ac_rfl
    _ = _ := by rw [← hBJ]

/-- The actual polynomial variables agree with the coordinates of relative affine space.
Source: affine-space definition and polynomial variable renaming
(blueprint: lem-trf-polynomial-log-chart-regularity). -/
private theorem polynomial_affine_chart (C : Type u) [CommRing C] (r : ℕ) :
    ∃ e : Spec (.of (MvPolynomial (Fin r) C)) ≅ 𝔸(ULift.{u} (Fin r); Spec (.of C)),
      e.hom ≫ (𝔸(ULift.{u} (Fin r); Spec (.of C)) ↘ Spec (.of C)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : C →+* MvPolynomial (Fin r) C)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (w : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin r) C))) (i : Fin r),
        strictHenselizationAffineCoordinate w r e (ULift.up i) =
          PolynomialLogChart.coordinate w i := by
  let q := (MvPolynomial.renameEquiv C (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r))
  let e := Scheme.Spec.mapIso q.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin r)) (.of C)).symm
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, AffineSpace.SpecIso_inv_over]
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [q]
  · intro Ω _ _ w i
    unfold strictHenselizationAffineCoordinate PolynomialLogChart.coordinate
      PolynomialLogChart.ringGerm
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, RingHom.comp_apply]
    congr 2
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    calc
      _ = (Spec.map (CommRingCat.ofHom q.toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin r)) C))).inv
            (MvPolynomial.X (ULift.up i))) :=
        congrArg (fun z ↦ (Spec.map (CommRingCat.ofHom q.toRingHom)).appTop z)
          (AffineSpace.SpecIso_inv_appTop_coord (.of C) (ULift.up i))
      _ = _ := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
          CommRingCat.comp_apply]
        congr 1
        simp [q]

/-- Polynomial logarithmic charts preserve fs log regularity, with their canonical
characteristic, stratum and dimension formulas. The two chart compatibility equations
specify the structural maps; `cW` presents the associated polynomial log structure.
Source: ILO VI 1.1--1.2 and 1.8--1.9, pp.69--71; Stacks Tags 031E and 00ON
(blueprint: lem-trf-polynomial-log-chart-regularity).

Proof:
1. The affine base gives a Noetherian coefficient ring, hence a Noetherian polynomial
ring and a locally Noetherian polynomial spectrum. Identify it with relative affine space.
The independent
`polynomial_log_chart_stalks` calculation gives fs charts, the characteristic,
its rank and the nonunit ideal. The projection is smooth by
`sbc-lem-affine-space-smooth`.
2. At a compatible geometric point the strict local map reflects units. Its chart unit
face is the base unit face times the free monoid on the nonvanishing coordinates.
`lem-trf-chart-face-localization-logification` identifies the characteristic with the
base characteristic times the free monoid on the vanishing coordinates. The displayed
formula on every `(p,n)` characterizes the canonical identification.
3. A chart element is a nonunit precisely when its base component is a nonunit or a
vanishing coordinate has positive exponent. The chart-stalk pushout then proves both
inclusions in `J = IB + (t_i : i ∈ K)`; base nonunit images lie in the maximal ideal.
4. Apply `lem-trf-smooth-geometric-stalk-algebra` to the polynomial projection and to
its coordinate-zero subscheme. This gives the Noetherian local rings, flat local maps,
regular closed fibres, and their dimension difference `|K|`. The base stratum is regular
by log regularity. Stacks 031E, `lem-weil-pbc-flat-over-regular-with-regular-fibre`, gives
regularity of the polynomial stratum.
5. Stacks 00ON, `lem-weil-pbc-flat-height-formula`, applied to both flat local maps gives
`dim B = dim A + dim F` and `dim (B/J) = dim (A/I) + dim F_K`. Combine these with base
log regularity and the fibre dimension difference. Group completion and rationalization
of the characteristic product add `|K|` to its rank. This proves log regularity everywhere.
The same empty products and empty sums handle `r = 0` and `K = ∅`; an empty base has no
geometric points and its polynomial spectrum is empty as well. -/
theorem polynomial_log_chart_regularity
    (C P : Type u) [CommRing C] [CommMonoid P]
    [hN : IsLocallyNoetherian (Spec (.of C))]
    (M : EtaleLogStructure (Spec (.of C))) (hfs : M.IsFineSaturated)
    (hreg : (FineSaturatedLogScheme.mk (Spec (.of C)) hN M hfs).IsLogRegular)
    (hP : IsFineSaturatedMonoid P) (α : P →* C)
    (cY : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of C))))))
    (hcY : M.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of C)))) cY)
    (hα : ∀ p : P, M.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of C))))) (cY p) =
      (Scheme.ΓSpecIso (.of C)).inv (α p))
    (r : ℕ) (N : EtaleLogStructure (Spec (.of (MvPolynomial (Fin r) C))))
    (cW : P × Multiplicative (Fin r →₀ ℕ) →*
      N.monoidSheaf.obj.obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C)))))))
    (hcW : N.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C))))) cW)
    (hβ : ∀ q : P × Multiplicative (Fin r →₀ ℕ),
      N.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C)))))) (cW q) =
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin r) C))).inv
          (PolynomialLogChart.structuralMap α r q)) :
    ∃ (hNW : IsLocallyNoetherian (Spec (.of (MvPolynomial (Fin r) C))))
      (hfsW : N.IsFineSaturated),
      (FineSaturatedLogScheme.mk _ hNW N hfsW).IsLogRegular ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (w : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin r) C)))
        (y : Spec (.of Ω) ⟶ Spec (.of C))
        (hy : w ≫ Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : C →+* MvPolynomial (Fin r) C)) = y),
        (∃ e : N.characteristic w ≃*
            M.characteristic y × Multiplicative (PolynomialLogChart.vanishingCoordinates w →₀ ℕ),
          ∀ (p : P) (n : Multiplicative (Fin r →₀ ℕ)),
            e (PolynomialLogChart.characteristicChart N cW w (p, n)) =
              (PolynomialLogChart.characteristicChart M cY y p,
                Multiplicative.ofAdd (n.toAdd.subtypeDomain
                  (fun i ↦ i ∈ PolynomialLogChart.vanishingCoordinates w)))) ∧
        ∃ (φ : Scheme.strictHenselizationRing y →+* Scheme.strictHenselizationRing w),
          φ = strictHenselizationRingMapAlong
            (Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : C →+* MvPolynomial (Fin r) C))) y w hy ∧
          PolynomialLogChart.nonunitIdeal N w =
            Ideal.map φ (PolynomialLogChart.nonunitIdeal M y) ⊔
              PolynomialLogChart.coordinateIdeal w ∧
          IsNoetherianRing (Scheme.strictHenselizationRing y) ∧
          IsNoetherianRing (Scheme.strictHenselizationRing w) ∧
          IsLocalRing (Scheme.strictHenselizationRing y) ∧
          IsLocalRing (Scheme.strictHenselizationRing w) ∧
          RingHom.Flat φ ∧ IsLocalHom φ ∧
          ∃ hIJ : PolynomialLogChart.nonunitIdeal M y ≤
              Ideal.comap φ (PolynomialLogChart.nonunitIdeal N w),
            IsNoetherianRing
              (Scheme.strictHenselizationRing y ⧸ PolynomialLogChart.nonunitIdeal M y) ∧
            IsLocalRing
              (Scheme.strictHenselizationRing y ⧸ PolynomialLogChart.nonunitIdeal M y) ∧
            IsNoetherianRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            IsLocalRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            RingHom.Flat (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w) φ hIJ) ∧
            IsLocalHom (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w) φ hIJ) ∧
            IsRegularRing (Scheme.strictHenselizationRing w ⧸
              Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y))) ∧
            IsRegularRing (Scheme.strictHenselizationRing w ⧸
              (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                PolynomialLogChart.coordinateIdeal w)) ∧
            ringKrullDim (Scheme.strictHenselizationRing w ⧸
              Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y))) =
              ringKrullDim (Scheme.strictHenselizationRing w ⧸
                (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                  PolynomialLogChart.coordinateIdeal w)) +
                    (PolynomialLogChart.vanishingCoordinates w).card ∧
            (∃ E : (Scheme.strictHenselizationRing w ⧸
                (PolynomialLogChart.nonunitIdeal N w ⊔
                  Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)))) ≃+*
                (Scheme.strictHenselizationRing w ⧸
                  (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                    PolynomialLogChart.coordinateIdeal w)),
              ∀ b : Scheme.strictHenselizationRing w,
                E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b) ∧
            IsRegularRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            ringKrullDim (Scheme.strictHenselizationRing w) =
              ringKrullDim
                (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) +
                  (M.characteristicRank y : WithBot ℕ∞) +
                    (PolynomialLogChart.vanishingCoordinates w).card := by
  classical
  have hC : IsNoetherianRing C := isLocallyNoetherian_Spec.mp hN
  have hNW : IsLocallyNoetherian (Spec (.of (MvPolynomial (Fin r) C))) := inferInstance
  obtain ⟨e, he, hcoords⟩ := polynomial_affine_chart C r
  let f := Spec.map (CommRingCat.ofHom (MvPolynomial.C : C →+* MvPolynomial (Fin r) C))
  have hsm : Smooth f := by
    dsimp only [f]
    rw [← he]
    have : Smooth (𝔸(ULift.{u} (Fin r); Spec (.of C)) ↘ Spec (.of C)) :=
      SmoothOfRelativeDimension.smooth (n := Nat.card (ULift.{u} (Fin r)))
        (𝔸(ULift.{u} (Fin r); Spec (.of C)) ↘ Spec (.of C))
    infer_instance
  obtain ⟨hfsW, hcharts⟩ :=
    polynomial_log_chart_stalks C P M hfs hP α cY hcY hα r N cW hcW hβ
  have hpoint : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (w : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin r) C)))
        (y : Spec (.of Ω) ⟶ Spec (.of C))
        (hy : w ≫ Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : C →+* MvPolynomial (Fin r) C)) = y),
        (∃ e : N.characteristic w ≃*
            M.characteristic y × Multiplicative (PolynomialLogChart.vanishingCoordinates w →₀ ℕ),
          ∀ (p : P) (n : Multiplicative (Fin r →₀ ℕ)),
            e (PolynomialLogChart.characteristicChart N cW w (p, n)) =
              (PolynomialLogChart.characteristicChart M cY y p,
                Multiplicative.ofAdd (n.toAdd.subtypeDomain
                  (fun i ↦ i ∈ PolynomialLogChart.vanishingCoordinates w)))) ∧
        ∃ (φ : Scheme.strictHenselizationRing y →+* Scheme.strictHenselizationRing w),
          φ = strictHenselizationRingMapAlong
            (Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : C →+* MvPolynomial (Fin r) C))) y w hy ∧
          PolynomialLogChart.nonunitIdeal N w =
            Ideal.map φ (PolynomialLogChart.nonunitIdeal M y) ⊔
              PolynomialLogChart.coordinateIdeal w ∧
          IsNoetherianRing (Scheme.strictHenselizationRing y) ∧
          IsNoetherianRing (Scheme.strictHenselizationRing w) ∧
          IsLocalRing (Scheme.strictHenselizationRing y) ∧
          IsLocalRing (Scheme.strictHenselizationRing w) ∧
          RingHom.Flat φ ∧ IsLocalHom φ ∧
          ∃ hIJ : PolynomialLogChart.nonunitIdeal M y ≤
              Ideal.comap φ (PolynomialLogChart.nonunitIdeal N w),
            IsNoetherianRing
              (Scheme.strictHenselizationRing y ⧸ PolynomialLogChart.nonunitIdeal M y) ∧
            IsLocalRing
              (Scheme.strictHenselizationRing y ⧸ PolynomialLogChart.nonunitIdeal M y) ∧
            IsNoetherianRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            IsLocalRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            RingHom.Flat (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w) φ hIJ) ∧
            IsLocalHom (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w) φ hIJ) ∧
            IsRegularRing (Scheme.strictHenselizationRing w ⧸
              Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y))) ∧
            IsRegularRing (Scheme.strictHenselizationRing w ⧸
              (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                PolynomialLogChart.coordinateIdeal w)) ∧
            ringKrullDim (Scheme.strictHenselizationRing w ⧸
              Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y))) =
              ringKrullDim (Scheme.strictHenselizationRing w ⧸
                (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                  PolynomialLogChart.coordinateIdeal w)) +
                    (PolynomialLogChart.vanishingCoordinates w).card ∧
            (∃ E : (Scheme.strictHenselizationRing w ⧸
                (PolynomialLogChart.nonunitIdeal N w ⊔
                  Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)))) ≃+*
                (Scheme.strictHenselizationRing w ⧸
                  (Ideal.map φ (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y)) ⊔
                    PolynomialLogChart.coordinateIdeal w)),
              ∀ b : Scheme.strictHenselizationRing w,
                E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b) ∧
            IsRegularRing
              (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) ∧
            ringKrullDim (Scheme.strictHenselizationRing w) =
              ringKrullDim
                (Scheme.strictHenselizationRing w ⧸ PolynomialLogChart.nonunitIdeal N w) +
                  (M.characteristicRank y : WithBot ℕ∞) +
                    (PolynomialLogChart.vanishingCoordinates w).card := by
    intro Ω _ _ w y hy
    obtain ⟨hchar, _, hJ, hI⟩ := hcharts Ω w y hy
    obtain ⟨hAN, hBN, hAL, hBL, hflat, hlocal, hFreg, _, hcoord⟩ :=
      smooth_geometric_stalk_algebra f y w hy
    let := hAN
    let := hBN
    let := hlocal
    let K := (PolynomialLogChart.vanishingCoordinates w).map
      (Equiv.ulift.symm.toEmbedding : Fin r ↪ ULift.{u} (Fin r))
    have hK (i : ULift.{u} (Fin r)) (hi : i ∈ K) :
        strictHenselizationAffineCoordinate w r e i ∈
          IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing w) := by
      rcases i with ⟨i⟩
      have hi' : i ∈ PolynomialLogChart.vanishingCoordinates w := by simpa [K] using hi
      rw [hcoords Ω w i]
      exact (Finset.mem_filter.mp hi').2
    have hspan : Ideal.span (Set.range
        (fun i : K ↦ strictHenselizationAffineCoordinate w r e i.1)) =
        PolynomialLogChart.coordinateIdeal w := by
      apply congrArg Ideal.span
      apply Set.ext
      intro b
      constructor
      · rintro ⟨⟨⟨i⟩, hi⟩, rfl⟩
        have hi' : i ∈ PolynomialLogChart.vanishingCoordinates w := by simpa [K] using hi
        exact ⟨⟨i, hi'⟩, (hcoords Ω w i).symm⟩
      · rintro ⟨i, rfl⟩
        have hi : ULift.up i.val ∈ K := by
          simpa only [K, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.ulift_apply] using i.property
        exact ⟨⟨ULift.up i.val, hi⟩, hcoords Ω w i.val⟩
    have hcard : K.card = (PolynomialLogChart.vanishingCoordinates w).card :=
      Finset.card_map _
    obtain ⟨hQN, hQL, hqflat, hFKreg, hE, hFdim⟩ :=
      hcoord r e he K hK (PolynomialLogChart.nonunitIdeal M y) hI
    rw [hspan, ← hJ] at hQN hQL
    rw [hspan] at hFKreg
    rw [hspan, ← hJ] at hE
    rw [hspan, hcard] at hFdim
    let := hQL
    let := hQN
    have : Nontrivial (Scheme.strictHenselizationRing y ⧸
        PolynomialLogChart.nonunitIdeal M y) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_of_lt (lt_of_le_of_lt hI (IsLocalRing.maximalIdeal.isMaximal _).lt_top))
    have hIL := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (PolynomialLogChart.nonunitIdeal M y)) Ideal.Quotient.mk_surjective
    have hIJ : PolynomialLogChart.nonunitIdeal M y ≤ Ideal.comap
        (strictHenselizationRingMapAlong f y w hy) (PolynomialLogChart.nonunitIdeal N w) := by
      rw [hJ]
      exact Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left)
    have hqflat' : (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w)
        (strictHenselizationRingMapAlong f y w hy) hIJ).Flat := by
      apply quotientMap_flat_congr (strictHenselizationRingMapAlong f y w hy)
        (PolynomialLogChart.nonunitIdeal M y) _ _ ?_ _ hIJ hqflat
      rw [hspan]
      exact hJ.symm
    have hquotlocal : IsLocalHom (Ideal.quotientMap (PolynomialLogChart.nonunitIdeal N w)
        (strictHenselizationRingMapAlong f y w hy) hIJ) := by
      let : IsLocalHom (Ideal.Quotient.mk (PolynomialLogChart.nonunitIdeal N w)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      refine ⟨?_⟩
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hu : IsUnit a := isUnit_of_map_unit
        ((Ideal.Quotient.mk (PolynomialLogChart.nonunitIdeal N w)).comp
          (strictHenselizationRingMapAlong f y w hy)) a ha
      exact (Ideal.Quotient.mk (PolynomialLogChart.nonunitIdeal M y)).isUnit_map hu
    obtain ⟨hbase, hbasedim⟩ :=
      (strict_log_regular_iff M y).mp (hreg Ω y)
    let := hbase
    let := hFKreg
    obtain ⟨E, hEclass⟩ := hE
    obtain ⟨hregular, hdimension⟩ := stratum_regular_dimension
      (strictHenselizationRingMapAlong f y w hy) hflat
      (PolynomialLogChart.nonunitIdeal M y) (PolynomialLogChart.nonunitIdeal N w) hIJ
      hqflat' E (M.characteristicRank y) (PolynomialLogChart.vanishingCoordinates w).card
      hbasedim hFdim
    exact ⟨hchar, strictHenselizationRingMapAlong f y w hy, rfl, hJ,
      hAN, hBN, hAL, hBL, hflat, hlocal, hIJ,
      inferInstance, hIL, hQN, hQL, hqflat', hquotlocal,
      hFreg, hFKreg, hFdim, ⟨E, hEclass⟩, hregular, hdimension⟩
  refine ⟨hNW, hfsW, ?_, hpoint⟩
  intro Ω _ _ w
  let y := w ≫ f
  obtain ⟨_, φ, _, _, _, _, _, _, _, _, hIJ,
    _, _, _, _, _, _, _, _, _, _, hregular, hdimension⟩ := hpoint Ω w y rfl
  apply (strict_log_regular_iff N w).mpr
  refine ⟨hregular, ?_⟩
  have hrank := (hcharts Ω w y rfl).2.1
  rw [hrank, WithBot.coe_add]
  simpa only [add_assoc, WithBot.coe_natCast] using hdimension


end AlgebraicGeometry
