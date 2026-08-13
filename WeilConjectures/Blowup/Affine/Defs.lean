/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.ReesGrading
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion

/-!

# The blow-up of an affine scheme along an ideal

We define the blow-up of `Spec A` along an ideal `I : Ideal A` as `Proj` of the Rees algebra
of `I` (with the grading of `WeilConjectures.Blowup.Affine.ReesGrading`), together with its
structure morphism to `Spec A` and its standard affine charts at the degree-one elements
`a·X`, `a ∈ I`.

## Main definitions

- `AlgebraicGeometry.AffineBlowup` — the blow-up `Proj (reesGrading I)`.
- `AlgebraicGeometry.AffineBlowup.toSpec` — the structure morphism `AffineBlowup I ⟶ Spec A`.
- `AlgebraicGeometry.AffineBlowup.chart` — the affine chart at a degree-one element.

## Main results

- `AlgebraicGeometry.AffineBlowup.iSup_basicOpen_reesX_eq_top` — the charts at the elements
  `a·X`, `a ∈ I` cover the blow-up.
- `AlgebraicGeometry.AffineBlowup.isIso_toSpec_of_eq_top` — blowing up the unit ideal is an
  isomorphism.

## Blueprint

This file implements `def:nagata-affine-blowup`, `lemma:nagata-rees-generators-cover-proj`
(in chart-cover form) and `lemma:nagata-affine-blowup-top` of the Nagata compactification
blueprint. The chart description of `def:nagata-homogeneous-away-to-chart` –
`prop:nagata-affine-blowup-chart` is carried by Mathlib's
`HomogeneousLocalization.Away`-based `Proj.awayι` API.

-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The blow-up of `Spec A` along the ideal `I`, defined as `Proj` of the Rees algebra
of `I`. (blueprint: `def:nagata-affine-blowup`) -/
noncomputable def AffineBlowup : Scheme.{u} :=
  Proj (reesGrading I)

namespace AffineBlowup

/-- The structure morphism `Bl_I (Spec A) ⟶ Spec A` of the affine blow-up.
(blueprint: `def:nagata-affine-blowup`) -/
noncomputable def toSpec : AffineBlowup I ⟶ Spec (.of A) :=
  Proj.toSpecZero (reesGrading I) ≫
    Spec.map (CommRingCat.ofHom (reesGradingZero I).toRingHom)

/-- The canonical ring homomorphism `A →+* Away (reesGrading I) x` through the degree-zero
subring. -/
noncomputable def awayAlgebraMap (x : reesAlgebra I) :
    A →+* HomogeneousLocalization.Away (reesGrading I) x :=
  (fromZeroRingHom (reesGrading I) (Submonoid.powers x)).comp
    (reesGradingZero I).toRingHom

/-- The affine chart of the blow-up at a degree-one element `x` of the Rees algebra.
(blueprint: `prop:nagata-affine-blowup-chart`) -/
noncomputable def chart (x : reesAlgebra I) (hx : x ∈ reesGrading I 1) :
    Spec (.of (HomogeneousLocalization.Away (reesGrading I) x)) ⟶ AffineBlowup I :=
  Proj.awayι (reesGrading I) x hx one_pos

instance (x : reesAlgebra I) (hx : x ∈ reesGrading I 1) :
    IsOpenImmersion (chart I x hx) := by
  unfold chart; infer_instance

lemma opensRange_chart (x : reesAlgebra I) (hx : x ∈ reesGrading I 1) :
    (chart I x hx).opensRange = Proj.basicOpen (reesGrading I) x :=
  Proj.opensRange_awayι ..

@[reassoc]
lemma chart_toSpec (x : reesAlgebra I) (hx : x ∈ reesGrading I 1) :
    chart I x hx ≫ toSpec I = Spec.map (CommRingCat.ofHom (awayAlgebraMap I x)) := by
  unfold chart toSpec awayAlgebraMap
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The basic opens at the degree-one elements `a·X`, `a ∈ I` cover the blow-up.
(blueprint: `lemma:nagata-rees-generators-cover-proj`) -/
lemma iSup_basicOpen_reesX_eq_top :
    ⨆ a : I, Proj.basicOpen (reesGrading I) (reesX I a a.2) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (reesGrading I) (fun a : I ↦ reesX I a a.2)
    (irrelevant_le_span_range_reesX I)

/-- Hom extensionality over the standard chart cover of the blow-up. -/
lemma hom_ext {Y : Scheme.{u}} {f g : AffineBlowup I ⟶ Y}
    (h : ∀ (a : A) (ha : a ∈ I),
      chart I (reesX I a ha) (reesX_mem I a ha) ≫ f =
        chart I (reesX I a ha) (reesX_mem I a ha) ≫ g) :
    f = g := by
  refine (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) I
      (fun a : I ↦ Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a a.2))))
      (fun a : I ↦ chart I (reesX I a a.2) (reesX_mem I a a.2))
      (fun x ↦ ?_) (fun a ↦ inferInstance)).hom_ext f g fun a ↦ ?_
  · have hx : x ∈ ⨆ a : I, Proj.basicOpen (reesGrading I) (reesX I a a.2) := by
      rw [iSup_basicOpen_reesX_eq_top]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    rw [← opensRange_chart I (reesX I a a.2) (reesX_mem I a a.2)] at ha
    obtain ⟨y, hy⟩ := ha
    exact ⟨a, y, hy⟩
  · let a' : I := a
    exact h a' a'.2

section Top

variable {I}

/-- For the unit ideal, the basic open at `1·X` is everything. -/
lemma basicOpen_reesX_one_eq_top (h : I = ⊤) :
    Proj.basicOpen (reesGrading I) (reesX I 1 (by rw [h]; trivial)) = ⊤ := by
  have h1 : (1 : A) ∈ I := by rw [h]; trivial
  have key : ⨆ _ : Unit, Proj.basicOpen (reesGrading I) (reesX I 1 h1) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top (reesGrading I) (fun _ ↦ reesX I 1 h1)
      ((irrelevant_le_span_range_reesX I).trans (Ideal.span_le.mpr ?_))
    rintro - ⟨a, rfl⟩
    change reesX I (a : A) a.2 ∈ _
    have hx1 : reesX I (a : A) a.2 =
        reesMonomial I (n := 0) (a : A) (by rw [pow_zero, Ideal.one_eq_top]; trivial) *
          reesX I 1 h1 := by
      apply Subtype.ext
      simp
    rw [hx1]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(), rfl⟩)
  rw [iSup_const] at key
  exact key

/-- For the unit ideal, the canonical map `A → Away (reesGrading I) (1·X)` is bijective. -/
lemma bijective_awayAlgebraMap_of_eq_top (h : I = ⊤) :
    Function.Bijective (awayAlgebraMap I (reesX I 1 (by rw [h]; trivial))) := by
  have h1 : (1 : A) ∈ I := by rw [h]; trivial
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hmk : awayAlgebraMap I (reesX I 1 h1) a =
        HomogeneousLocalization.mk ⟨0, reesGradingZero I a, 1, one_mem _⟩ := rfl
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero, hmk,
      HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_zero_iff] at ha
    obtain ⟨⟨-, k, rfl⟩, hc⟩ := ha
    have hcoeff := congrArg (fun p : reesAlgebra I ↦ (p : Polynomial A).coeff k) hc
    simpa [Polynomial.monomial_pow, Polynomial.monomial_mul_C,
      Polynomial.coeff_monomial] using hcoeff
  · intro z
    obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesGrading I)
      (reesX_mem I 1 h1) z
    obtain ⟨b, hb, rfl⟩ := (mem_reesGrading_iff_exists I).mp hy
    refine ⟨b, ?_⟩
    have hmk : awayAlgebraMap I (reesX I 1 h1) b =
        HomogeneousLocalization.mk ⟨0, reesGradingZero I b, 1, one_mem _⟩ := rfl
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk, hmk,
      HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [Polynomial.monomial_pow, Polynomial.monomial_mul_C, smul_eq_mul]

/-- The blow-up of the unit ideal is trivial: the structure morphism is an isomorphism.
(blueprint: `lemma:nagata-affine-blowup-top`) -/
theorem isIso_toSpec_of_eq_top (h : I = ⊤) : IsIso (toSpec I) := by
  have h1 : (1 : A) ∈ I := by rw [h]; trivial
  have hchart : IsIso (chart I (reesX I 1 h1) (reesX_mem I 1 h1)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [opensRange_chart]
    exact basicOpen_reesX_one_eq_top h
  have hcomp : IsIso (chart I (reesX I 1 h1) (reesX_mem I 1 h1) ≫ toSpec I) := by
    rw [chart_toSpec, isIso_SpecMap_iff]
    simpa using bijective_awayAlgebraMap_of_eq_top h
  exact IsIso.of_isIso_comp_left (chart I (reesX I 1 h1) (reesX_mem I 1 h1)) (toSpec I)

end Top

end AffineBlowup

end AlgebraicGeometry
