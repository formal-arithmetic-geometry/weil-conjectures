/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Compactification.StrictTransformChartModel
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Flat pullback of blowup charts and exceptional fibres

Source: Stacks Project, divisors.tex, Tags 0804 and 0805;
morphisms.tex, Tag 02GL(2) (blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions).

The chart predicate records the restriction of the specified global comparison, its
fraction formula, extended ideals, and the induced maps on overlap localizations.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- The fraction generator `c/a` in the existing chart algebra.
Source: Stacks 0804 (blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions). -/
noncomputable def AffineBlowup.chartGenerator {A : Type u} [CommRing A]
    (I : Ideal A) (a : A) (c : I) : AffineBlowup.chartRing I a :=
  ⟨AffineBlowup.chartFraction a 1 c, Algebra.subset_adjoin ⟨c, rfl⟩⟩

private theorem strictChartMap_injective_of_flat {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (a : A) (ha : a ∈ I) :
    Function.Injective (AffineBlowup.strictChartMap B I a ha) := by
  have hr : IsSMulRegular (AffineBlowup.chartRing I a) a := by
    intro x y hxy
    apply Subtype.ext
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away a) a).isRegular.left
    simpa only [Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] using
      congrArg Subtype.val hxy
  have hrB : IsSMulRegular (AffineBlowup.BaseChangeChart B I a) (algebraMap A B a) :=
    hr.of_flat_of_isBaseChange (TensorProduct.isBaseChange A (AffineBlowup.chartRing I a) B)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have ht : z ∈ AffineBlowup.baseChangeChartTorsion B I a := by
    rw [← AffineBlowup.ker_strictChartMap B I ha, RingHom.mem_ker]
    exact hz
  obtain ⟨n, hn⟩ := Submodule.mem_powTorsion_iff.mp ht
  apply (hrB.pow n).right_eq_zero_of_smul
  simpa only [Algebra.smul_def, map_pow, ← IsScalarTower.algebraMap_apply] using hn

private theorem chartRingιOfEq_eq {A : Type u} [CommRing A] (I : Ideal A)
    {a : A} (ha : a ∈ I) {x : reesAlgebra I} (e : x = reesX I a ha)
    (hx : x ∈ reesGrading I 1) :
    AffineBlowup.chartRingιOfEq I ha e hx = AffineBlowup.chartRingι I ha := by
  subst x
  rfl

private theorem chartRingι_hom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (hJ : I.map (algebraMap A B) = J)
    (a : A) (ha : a ∈ I) (hb : algebraMap A B a ∈ J)
    (e : (B ⊗[A] AffineBlowup.chartRing I a) ≃ₐ[B]
      AffineBlowup.chartRing J (algebraMap A B a))
    (he : ∀ (b : B) (z : AffineBlowup.chartRing I a),
      (e (b ⊗ₜ z) : Localization.Away (algebraMap A B a)) =
        algebraMap B _ b * Localization.awayMap (algebraMap A B) a z) :
    AffineBlowup.chartRingι J hb ≫ AffineBlowup.hom (algebraMap A B) hJ =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          AffineBlowup.chartRingι I ha := by
  subst J
  have heq : e.toRingHom = (AffineBlowup.strictChartMap B I a ha).toRingHom := by
    apply RingHom.ext
    intro z
    apply Subtype.ext
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero]
    | tmul b z => exact he b z
    | add z w hz hw =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hz hw
  have H := congrArg (fun t ↦ t ≫ pullback.snd _ _)
    (AffineBlowup.isPullback_baseChangeChartι B I ha).w
  simp only [Category.assoc, AffineBlowup.baseChangeChartι_snd,
    pullback.lift_snd] at H
  rw [AffineBlowup.baseChangeChartRingι, chartRingιOfEq_eq] at H
  rw [heq, CommRingCat.ofHom_comp, Spec.map_comp]
  exact H.symm

private theorem chartRingι_preimage {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (J : Ideal B) (hJ : I.map φ = J)
    (a : A) (ha : a ∈ I) (hb : φ a ∈ J) :
    AffineBlowup.hom φ hJ ⁻¹ᵁ (AffineBlowup.chartRingι I ha).opensRange =
      (AffineBlowup.chartRingι J hb).opensRange := by
  rw [AffineBlowup.opensRange_chartRingιOfEq, AffineBlowup.opensRange_chartRingιOfEq,
    AffineBlowup.opensRange_chart, AffineBlowup.opensRange_chart]
  change Proj.map (reesGrading.hom φ hJ) _ ⁻¹ᵁ _ = _
  rw [Proj.map_preimage_basicOpen, reesGrading.hom_reesX]

private theorem map_ideal_algEquiv {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra B D]
    (I : Ideal A) (J : Ideal B) (hJ : I.map (algebraMap A B) = J) (e : C ≃ₐ[B] D) :
    Ideal.map e.toRingHom (I.map (algebraMap A C)) = J.map (algebraMap B D) := by
  have heA : e.toRingHom.comp (algebraMap A C) =
      (algebraMap B D).comp (algebraMap A B) := by
    apply RingHom.ext
    intro r
    change e (algebraMap A C r) = algebraMap B D (algebraMap A B r)
    exact (congrArg e (IsScalarTower.algebraMap_apply A B C r)).trans (e.commutes _)
  rw [Ideal.map_map, heA, ← Ideal.map_map, hJ]

private theorem away_equiv_formula {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) :
    ∃ w : Localization.Away t ≃+* Localization.Away (e t),
      ∀ (z : R) (n : ℕ),
        w (Localization.mk z ⟨t ^ n, n, rfl⟩) =
          IsLocalization.mk' (Localization.Away (e t)) (e z)
            (⟨(e t) ^ n, n, rfl⟩ : Submonoid.powers (e t)) := by
  have hp : (Submonoid.powers t).map e.toMonoidHom = Submonoid.powers (e t) :=
    Submonoid.map_powers _ _
  refine ⟨IsLocalization.ringEquivOfRingEquiv (Localization.Away t)
    (Localization.Away (e t)) e hp, ?_⟩
  intro z n
  rw [Localization.mk_eq_mk', IsLocalization.ringEquivOfRingEquiv_mk']
  congr 1
  exact Subtype.ext (map_pow e t n)

namespace Scheme.IdealSheafData

/-- The standard chart `Spec A[I/a] → Bl_I X`, using the recorded homogeneous chart
identification and the global affine-open embedding.
Source: Stacks 0804 (blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions). -/
noncomputable def fractionChartι {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    Spec (.of (AffineBlowup.chartRing (I.ideal U) a)) ⟶ I.blowup :=
  Spec.map (CommRingCat.ofHom
    (AffineBlowup.homogeneousAwayEquivChart (I.ideal U) ha).toRingHom) ≫
    AffineBlowup.chart (I.ideal U) (reesX (I.ideal U) a ha)
      (reesX_mem (I.ideal U) a ha) ≫ I.blowupι U

/-- The full affine restriction assertion, with the algebra structure supplied by the
actual map on affine sections. The `letI` only installs that canonical ring-map algebra;
no proposition or conclusion is hidden in it.
Source: Stacks 0804, 0805 and 01N2
(blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions). -/
def BlowupChartBaseChange {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [Flat g] (U : X.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ U.1) : Prop :=
  letI := (g.appLE U.1 V.1 h).hom.toAlgebra
  ∀ (a : Γ(X, U.1)) (ha : a ∈ I.ideal U),
    ∃ (hb : algebraMap Γ(X, U.1) Γ(Y, V.1) a ∈ (I.comap g).ideal V)
      (e : (Γ(Y, V.1) ⊗[Γ(X, U.1)] AffineBlowup.chartRing (I.ideal U) a) ≃ₐ[Γ(Y, V.1)]
        AffineBlowup.chartRing ((I.comap g).ideal V)
          (algebraMap Γ(X, U.1) Γ(Y, V.1) a)),
      (∀ (b : Γ(Y, V.1)) (z : AffineBlowup.chartRing (I.ideal U) a),
        (e (b ⊗ₜ z) : Localization.Away (algebraMap Γ(X, U.1) Γ(Y, V.1) a)) =
          algebraMap Γ(Y, V.1) _ b *
            Localization.awayMap (algebraMap Γ(X, U.1) Γ(Y, V.1)) a z) ∧
      (I.comap g).fractionChartι V _ hb ≫ I.blowupFlatBaseChange g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom
          (e.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := Γ(X, U.1))
              (A := Γ(Y, V.1)) (B := AffineBlowup.chartRing (I.ideal U) a)).toRingHom)) ≫
            I.fractionChartι U a ha ∧
      (I.comap g).fractionChartι V _ hb ≫ (I.comap g).blowupMap =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V.1) _)) ≫ V.2.fromSpec ∧
      Set.range ((I.comap g).fractionChartι V _ hb) =
        (I.blowupFlatBaseChange g ≫ pullback.fst _ _) ⁻¹'
          Set.range (I.fractionChartι U a ha) ∩
        (I.comap g).blowupMap ⁻¹' (V.1 : Set Y) ∧
      Ideal.map e.toRingHom
        ((I.ideal U).map (algebraMap Γ(X, U.1) _)) =
          ((I.comap g).ideal V).map (algebraMap Γ(Y, V.1) _) ∧
      (∀ c : I.ideal U,
        ∃ w : Localization.Away (1 ⊗ₜ[Γ(X, U.1)]
            AffineBlowup.chartGenerator (I.ideal U) a c) ≃+*
          Localization.Away (e (1 ⊗ₜ[Γ(X, U.1)]
            AffineBlowup.chartGenerator (I.ideal U) a c)),
          ∀ (z : Γ(Y, V.1) ⊗[Γ(X, U.1)] AffineBlowup.chartRing (I.ideal U) a)
            (n : ℕ),
            w (Localization.mk z
              ⟨(1 ⊗ₜ[Γ(X, U.1)] AffineBlowup.chartGenerator (I.ideal U) a c) ^ n,
                n, rfl⟩) =
              IsLocalization.mk' (Localization.Away (e (1 ⊗ₜ[Γ(X, U.1)]
                AffineBlowup.chartGenerator (I.ideal U) a c))) (e z)
                (⟨(e (1 ⊗ₜ[Γ(X, U.1)]
                  AffineBlowup.chartGenerator (I.ideal U) a c)) ^ n, n, rfl⟩ :
                  Submonoid.powers (e (1 ⊗ₜ[Γ(X, U.1)]
                    AffineBlowup.chartGenerator (I.ideal U) a c))))

/-- Chartwise flat pullback, including fractions, structural maps, centre ideals and
localizations on overlaps.
Source: Stacks 0804, 0805; constructions.tex 01N2, 01M4, 01MY
(blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions).

Proof, steps 1--4 of the node:
1. `def-nagata-flat-pullback-rees-map` and `lemma-nagata-flat-pullback-rees` give
   the coefficientwise graded base change, taking `at` to its image. The specified
   `def-nagata-blowup-flat-base-change-map` is an isomorphism by
   `thm-nagata-blowup-flat-base-change`; `lem-nagata-affine-proj-scalar-extension`
   identifies the inverse images of standard opens and their restriction maps.
2. Apply `lem-nagata-homogeneous-localization-scalar-extension` and the map of
   `def-nagata-homogeneous-away-to-chart`. Its well-definedness, injectivity and
   surjectivity are `lemma-nagata-homogeneous-away-to-chart` and its -injective
   and -surjective nodes. Fractions map coefficientwise, including degree zero.
3. `lemma-nagata-extended-ideal-affine-chart` identifies the extended ideals.
   Their generators agree since J=IB; `lemma-nagata-chart-extended-ideal-principal`
   also identifies them as (a) and (the image of a).
4. `lemma-nagata-proj-chart-ring-cocycle` identifies overlaps with localization
   at c/a. Localizing the same ring isomorphism sends z/(c/a)^n to its indicated
   image, and the common homogeneous restriction gives agreement on overlaps
   and on triple overlaps. No denominator is assumed nonzero or regular. -/
theorem blowup_flat_chart_restrictions {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (I : X.IdealSheafData) (hI : Scheme.Modules.IsQuasiCoherentFiniteType I.toModules)
    (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1) :
    I.BlowupChartBaseChange g U V h := by
  have _ := hI
  let := (g.appLE U.1 V.1 h).hom.toAlgebra
  let A := Γ(X, U.1)
  let B := Γ(Y, V.1)
  have hJ : (I.ideal U).map (algebraMap A B) = (I.comap g).ideal V :=
    I.map_ideal_appLE g h
  have : Module.Flat A B :=
    HasRingHomProperty.appLE (P := @Flat) g inferInstance U V h
  let ρ := I.blowupFlatBaseChange g ≫ pullback.fst _ _
  have hρ : (I.comap g).blowupMap ≫ g = ρ ≫ I.blowupMap := by
    dsimp only [ρ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ g) (I.blowupFlatBaseChangeIso_hom_snd g).symm
  intro a ha
  have hb : algebraMap A B a ∈ (I.comap g).ideal V := by
    rw [← hJ]
    exact Ideal.mem_map_of_mem _ ha
  have he : ∃ e : (B ⊗[A] AffineBlowup.chartRing (I.ideal U) a) ≃ₐ[B]
        AffineBlowup.chartRing ((I.comap g).ideal V) (algebraMap A B a),
      ∀ (b : B) (z : AffineBlowup.chartRing (I.ideal U) a),
        (e (b ⊗ₜ z) : Localization.Away (algebraMap A B a)) =
          algebraMap B _ b * Localization.awayMap (algebraMap A B) a z := by
    rw [← hJ]
    refine ⟨AlgEquiv.ofBijective (AffineBlowup.strictChartMap B (I.ideal U) a ha)
      ⟨strictChartMap_injective_of_flat (I.ideal U) a ha,
        AffineBlowup.strictChartMap_surjective B (I.ideal U) ha⟩, ?_⟩
    intro b z
    rfl
  obtain ⟨e, he⟩ := he
  refine ⟨hb, e, he, ?_, ?_, ?_, ?_, ?_⟩
  · change (AffineBlowup.chartRingι _ hb ≫ (I.comap g).blowupι V) ≫ ρ = _
    rw [Category.assoc, I.blowupι_comp_of_le_preimage g hρ U V h, ← Category.assoc]
    change (AffineBlowup.chartRingι _ hb ≫ AffineBlowup.hom (algebraMap A B) hJ) ≫
      I.blowupι U = _
    rw [chartRingι_hom (I.ideal U) _ hJ a ha hb e he]
    rfl
  · change (AffineBlowup.chartRingι _ hb ≫ (I.comap g).blowupι V) ≫
      (I.comap g).blowupMap = _
    rw [Category.assoc, (I.comap g).blowupι_comp_blowupMap V,
      ← Category.assoc, AffineBlowup.chartRingιOfEq_toSpec]
  · let f := AffineBlowup.hom (algebraMap A B) hJ
    let j := (I.comap g).blowupι V
    let k := I.blowupι U
    let cA := AffineBlowup.chartRingι (I.ideal U) ha
    let cB := AffineBlowup.chartRingι ((I.comap g).ideal V) hb
    have hlocal : j ≫ ρ = f ≫ k := I.blowupι_comp_of_le_preimage g hρ U V h
    have hpre : f ⁻¹ᵁ cA.opensRange = cB.opensRange :=
      chartRingι_preimage (algebraMap A B) (I.ideal U) _ hJ a ha hb
    have hV : (I.comap g).blowupMap ⁻¹' (V.1 : Set Y) = Set.range j :=
      congrArg SetLike.coe ((I.comap g).blowupMap_preimage V)
    change Set.range (cB ≫ j) = ρ ⁻¹' Set.range (cA ≫ k) ∩ _
    rw [hV]
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨?_, ⟨cB p, rfl⟩⟩
      have hc : cB p ∈ f ⁻¹ᵁ cA.opensRange := by
        rw [hpre]
        exact ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := hc
      refine ⟨q, ?_⟩
      change (cA ≫ k) q = (j ≫ ρ) (cB p)
      rw [hlocal]
      exact congrArg k hq
    · rintro ⟨⟨q, hq⟩, t, rfl⟩
      have hc : f t ∈ cA.opensRange := by
        refine ⟨q, ?_⟩
        apply k.isOpenEmbedding.injective
        change (cA ≫ k) q = (f ≫ k) t
        rw [← hlocal]
        exact hq
      have ht : t ∈ cB.opensRange := by
        rw [← hpre]
        exact hc
      obtain ⟨p, hp⟩ := ht
      exact ⟨p, congrArg j hp⟩
  · exact map_ideal_algEquiv (I.ideal U) _ hJ e
  · intro c
    exact away_equiv_formula e.toRingEquiv
      ((1 : B) ⊗ₜ[A] AffineBlowup.chartGenerator (I.ideal U) a c)


/-- The exceptional fibre is the old fibre extended along the actual residue-field map.
The two projection equations specify the canonical isomorphism, and express compatibility
with every chart restriction of the same blowup comparison.
Source: Stacks 0805, fibre-product universal property
(blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions).

Proof, node step 5: apply `def-pc-fibre-product` to the blowup comparison of steps
1--4. By `def-weil-residue-field`, Spec κ(y) → X factors through Spec κ(g(y)).
Both iterated pullbacks classify pairs of maps to the old blowup and Spec κ(y)
with the same composite to X. The maps in both directions have identity composites
by uniqueness. The same projection equations after restricting to any chart give
chart compatibility. The map κ(g(y)) → κ(y) is retained throughout. -/
theorem blowup_flat_fiber_residue {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (I : X.IdealSheafData) (hI : Scheme.Modules.IsQuasiCoherentFiniteType I.toModules)
    (y : Y) :
    ∃ e : (I.comap g).blowupMap.fiber y ≅
        pullback (I.blowupMap.fiberToSpecResidueField (g y))
          (Spec.map (g.residueFieldMap y)),
      e.hom ≫ pullback.fst _ _ ≫ I.blowupMap.fiberι (g y) =
        (I.comap g).blowupMap.fiberι y ≫
          I.blowupFlatBaseChange g ≫ pullback.fst _ _ ∧
      e.hom ≫ pullback.snd _ _ = (I.comap g).blowupMap.fiberToSpecResidueField y := by
  have _ := hI
  have hs : IsPullback (I.blowupFlatBaseChange g ≫ pullback.fst _ _)
      ((I.comap g).blowupMap) I.blowupMap g := by
    apply IsPullback.of_iso_pullback (i := I.blowupFlatBaseChangeIso g)
    · constructor
      rw [Category.assoc, pullback.condition,
        ← I.blowupFlatBaseChangeIso_hom_snd g]
      rfl
    · rfl
    · exact I.blowupFlatBaseChangeIso_hom_snd g
  let H := isPullback_fiberToSpecResidueField_of_isPullback hs y
  refine ⟨H.isoPullback, ?_, H.isoPullback_hom_snd⟩
  rw [← Category.assoc, H.isoPullback_hom_fst]
  exact pullback.lift_fst _ _ _

/-- Near a point over a closed reduced centre, an etale pullback has precisely the
reduced-point ideal as its centre. The map from Spec κ(y) is the canonical point map
factored through the neighbourhood; no equality of residue fields is assumed.
Source: Stacks 02GL(2), 01JU, 0805
(blueprint: lem-sfb-flat-pullback-blowup-chart-restrictions).

Proof, node step 6: by `lem-pc-closed-subscheme-base-change-ideal-image` the
pullback F of Spec κ(g(y)) is a closed subscheme of Y with ideal I.comap g.
By `def-pc-scheme-fibre` its space is the fibre. The theorem
`lem-weil-pbc-etale-fibre-discrete-separable-points` makes F a disjoint union of
field spectra. Remove the closed union of all components other than y from Y.
On the remaining open the closed subscheme F is exactly Spec κ(y), since a closed
immersion preserves residue fields. Its kernel ideal is the restricted extended
ideal. Applying steps 1--5 after this open restriction gives the comparison for
blowing up y itself. -/
theorem etale_blowup_reduced_point_neighbourhood {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Etale g] (I : X.IdealSheafData)
    (hI : Scheme.Modules.IsQuasiCoherentFiniteType I.toModules) (y : Y)
    (hx : IsClosed ({g y} : Set X)) (hcentre : I = (X.fromSpecResidueField (g y)).ker) :
    ∃ (V : Y.Opens), y ∈ V ∧
      ∃ i : Spec (Y.residueField y) ⟶ V.toScheme,
        IsClosedImmersion i ∧ i ≫ V.ι = Y.fromSpecResidueField y ∧
          (I.comap g).comap V.ι = i.ker := by
  classical
  have _ := hI
  have : IsClosedImmersion (X.fromSpecResidueField (g y)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let F := g.fiber (g y)
  let k : F ⟶ Y := g.fiberι (g y)
  let z : F := g.asFiber y
  have hkz : k z = y := g.fiberι_asFiber y
  have : IsClosedImmersion k := inferInstanceAs
    (IsClosedImmersion (pullback.fst g (X.fromSpecResidueField (g y))))
  have : DiscreteTopology F := (g.etale_fibre_discrete_separable_points (g y)).1
  have : Etale (g.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (Etale (pullback.snd g (X.fromSpecResidueField (g y))))
  have : IsReduced F := isReduced_of_etale (g.fiberToSpecResidueField (g y))
  let V : Y.Opens := ⟨(k '' ({z}ᶜ : Set F))ᶜ,
    (k.isClosedMap _ (isClosed_discrete _)).isOpen_compl⟩
  have hy : y ∈ V := by
    rintro ⟨w, hw, hwk⟩
    have : w = z := k.isClosedEmbedding.injective (hwk.trans hkz.symm)
    exact hw this
  let i := IsOpenImmersion.lift V.ι (Y.fromSpecResidueField y) (by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hy)
  have hi : i ≫ V.ι = Y.fromSpecResidueField y := IsOpenImmersion.lift_fac _ _ _
  have hiy : IsClosed ({y} : Set Y) := by
    have hr : k '' ({z} : Set F) = {y} := by simp [hkz]
    rw [← hr]
    exact k.isClosedMap _ (isClosed_discrete _)
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hiy
  have : IsClosedImmersion (i ≫ V.ι) := hi ▸ inferInstance
  have : IsClosedImmersion i := .of_comp i V.ι
  refine ⟨V, hy, i, inferInstance, hi, ?_⟩
  let q := pullback.fst V.ι k
  have : IsReduced (pullback V.ι k) :=
    isReduced_of_isOpenImmersion (pullback.snd V.ι k)
  have hqrange : Set.range q = {⟨y, hy⟩} := by
    rw [show Set.range q = V.ι ⁻¹' Set.range k from Scheme.Pullback.range_fst V.ι k]
    ext v
    constructor
    · rintro ⟨w, hw⟩
      have hwz : w = z := by
        by_contra hn
        exact v.property ⟨w, hn, hw⟩
      apply Subtype.ext
      exact hw.symm.trans (hwz ▸ hkz)
    · rintro rfl
      exact ⟨z, hkz⟩
  have hirange : Set.range i = {⟨y, hy⟩} := by
    ext v
    constructor
    · rintro ⟨t, rfl⟩
      apply Subtype.ext
      change (i ≫ V.ι) t = y
      rw [hi, Scheme.fromSpecResidueField_apply]
    · rintro rfl
      refine ⟨default, ?_⟩
      apply Subtype.ext
      change (i ≫ V.ι) default = y
      rw [hi, Scheme.fromSpecResidueField_apply]
  have hJ : I.comap g = k.ker := by
    rw [hcentre]
    exact (ker_fst_of_isClosedImmersion (X.fromSpecResidueField (g y)) g).symm
  rw [hJ, ← ker_fst_of_isClosedImmersion k V.ι]
  change q.ker = i.ker
  rw [q.ker_eq_vanishingIdeal, i.ker_eq_vanishingIdeal, hqrange, hirange]

end Scheme.IdealSheafData
end AlgebraicGeometry
