/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.StrictTransformChart
public import WeilConjectures.Compactification.StrictTransformBlowup

/-!

# The chart model of the strict transform

Let `f : Y ⟶ X` be a morphism of schemes, `I` an ideal sheaf on `X` and `X' = Bl_I(X)`. For
affine opens `U = Spec A ⊆ X`, `V = Spec B ⊆ f⁻¹ U` and `a ∈ I(U)`, the fibre product
`Y ×_X X'` has the affine chart `Spec C_a(A, B, I(U)) = Spec (B ⊗_A A[I/a])`. We show that the
strict transform of `Y` meets this chart in the closed subscheme `Spec C_a^st(A, B, I(U))` cut out
by the `a`-power torsion, and that the strict transform is the closed subscheme glued from these
chart models.

## Main definitions

- `AlgebraicGeometry.AffineBlowup.baseChangeChartι`: the chart
  `Spec C_a(A, B, I) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.StrictTransformChart`: the chart data `(U, V, a)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.StrictTransformChart.ι`: the chart
  `Spec C_a ⟶ Y ×_X Bl_I(X)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.strictTransformChartModel`: the closed subscheme of
  `Y ×_X Bl_I(X)` glued from the chart models `Spec C_a^st ⊆ Spec C_a`.

## Main results

- `AlgebraicGeometry.AffineBlowup.isPullback_baseChangeChartι`: over the chart at `a`, the
  blow-up of `Spec B` along `IB` is `Spec` of the chart ring `B[IB/b]`, mapping to the chart by
  `σ_a`.
- `AlgebraicGeometry.Scheme.IdealSheafData.StrictTransformChart.comap_ker_strictTransformι`: the
  strict transform meets the chart `Spec C_a` in `Spec C_a^st`.
- `AlgebraicGeometry.Scheme.IdealSheafData.strictTransformChartModel_eq`: the glued chart model
  is the strict transform.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry

lemma Scheme.Hom.ker_specMap_eq_of_ker_eq {R S T : CommRingCat.{u}} (σ : R ⟶ S) (τ : R ⟶ T)
    (h : RingHom.ker σ.hom = RingHom.ker τ.hom) : (Spec.map σ).ker = (Spec.map τ).ker := by
  have key : ∀ {S : CommRingCat.{u}} (σ : R ⟶ S), RingHom.ker (Spec.map σ).appTop.hom =
      (RingHom.ker σ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
    intro S σ
    ext x
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, ← map_eq_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).1,
      ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine, key, key, h]

/-- **Flat base change of kernels along a cartesian square**: for a quasi-compact `f` and a flat
`q`, the kernel of the base change of `f` along `q` is the pullback of the kernel of `f`. -/
lemma Scheme.Hom.comap_ker_of_isPullback {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} [QuasiCompact f]
    {q : X' ⟶ X} [Flat q] {f' : Y' ⟶ X'} {p : Y' ⟶ Y} (h : IsPullback p f' f q) :
    f.ker.comap q = f'.ker := by
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.map_comap_of_isPullback _ h,
    Scheme.IdealSheafData.comap_bot, Scheme.IdealSheafData.map_bot]

namespace AffineBlowup

section Chart

variable {A : Type u} [CommRing A] (I : Ideal A) {a : A} (ha : a ∈ I)

/-- The isomorphism `θ_a : Away (reesGrading I) x ≃ A[I/a]` for a degree-one element `x` of the
Rees algebra equal to `a·X`. -/
def homogeneousAwayEquivChartOfEq {x : reesAlgebra I} (e : x = reesX I a ha) :
    HomogeneousLocalization.Away (reesGrading I) x ≃+* chartRing I a := by
  subst e
  exact homogeneousAwayEquivChart I ha

lemma coe_homogeneousAwayEquivChartOfEq_mk {x : reesAlgebra I} (e : x = reesX I a ha)
    (hx : x ∈ reesGrading I 1) {n : ℕ} (y : A) (hy : y ∈ I ^ n)
    (h : reesMonomial I y hy ∈ reesGrading I (n • 1)) :
    (homogeneousAwayEquivChartOfEq I ha e (Away.mk (reesGrading I) hx n (reesMonomial I y hy) h) :
      Localization.Away a) = chartFraction a n y := by
  subst e
  exact coe_homogeneousAwayToChart_mk I ha y hy h

lemma homogeneousAwayEquivChartOfEq_awayAlgebraMap {x : reesAlgebra I} (e : x = reesX I a ha)
    (r : A) : homogeneousAwayEquivChartOfEq I ha e (awayAlgebraMap I x r) = algebraMap A _ r := by
  subst e
  exact homogeneousAwayToChart_awayAlgebraMap I ha r

/-- The chart `Spec A[I/a] ⟶ Bl_I(Spec A)` at a degree-one element `x = a·X`, through the
isomorphism `θ_a : Away (reesGrading I) x ≃ A[I/a]`. -/
def chartRingιOfEq {x : reesAlgebra I} (e : x = reesX I a ha) (hx : x ∈ reesGrading I 1) :
    Spec (.of (chartRing I a)) ⟶ AffineBlowup I :=
  Spec.map (CommRingCat.ofHom (homogeneousAwayEquivChartOfEq I ha e).toRingHom) ≫ chart I x hx

instance {x : reesAlgebra I} (e : x = reesX I a ha) (hx : x ∈ reesGrading I 1) :
    IsOpenImmersion (chartRingιOfEq I ha e hx) := by
  have : IsIso (CommRingCat.ofHom (homogeneousAwayEquivChartOfEq I ha e).toRingHom) :=
    (RingEquiv.toCommRingCatIso (homogeneousAwayEquivChartOfEq I ha e)).isIso_hom
  unfold chartRingιOfEq
  infer_instance

@[reassoc]
lemma chartRingιOfEq_toSpec {x : reesAlgebra I} (e : x = reesX I a ha)
    (hx : x ∈ reesGrading I 1) :
    chartRingιOfEq I ha e hx ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (algebraMap A (chartRing I a))) := by
  unfold chartRingιOfEq
  rw [Category.assoc, chart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact congrArg Subtype.val (homogeneousAwayEquivChartOfEq_awayAlgebraMap I ha e r)

lemma opensRange_chartRingιOfEq {x : reesAlgebra I} (e : x = reesX I a ha)
    (hx : x ∈ reesGrading I 1) :
    (chartRingιOfEq I ha e hx).opensRange = (chart I x hx).opensRange := by
  have : IsIso (CommRingCat.ofHom (homogeneousAwayEquivChartOfEq I ha e).toRingHom) :=
    (RingEquiv.toCommRingCatIso (homogeneousAwayEquivChartOfEq I ha e)).isIso_hom
  unfold chartRingιOfEq
  rw [Scheme.Hom.opensRange_comp_of_isIso]

/-- The chart `Spec A[I/a] ⟶ Bl_I(Spec A)` at `a ∈ I`. -/
abbrev chartRingι : Spec (.of (chartRing I a)) ⟶ AffineBlowup I :=
  chartRingιOfEq I ha rfl (reesX_mem I a ha)

end Chart

variable {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) {a : A}
  (ha : a ∈ I)

/-- The chart `Spec C_a(A, B, I) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)` of the base change of the
blow-up of `Spec A` along `I` at `a ∈ I`, where `C_a(A, B, I) = B ⊗_A A[I/a]`. -/
def baseChangeChartι :
    Spec (.of (BaseChangeChart B I a)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (toSpec I) :=
  (pullbackSpecIso A B (chartRing I a)).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (chartRingι I ha) (𝟙 _) (by simp)
      (by rw [chartRingιOfEq_toSpec, Category.comp_id])

instance : IsOpenImmersion (baseChangeChartι B I ha) := by
  unfold baseChangeChartι
  infer_instance

@[reassoc (attr := simp)]
lemma baseChangeChartι_fst :
    baseChangeChartι B I ha ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap B (BaseChangeChart B I a))) := by
  unfold baseChangeChartι
  rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullbackSpecIso_inv_fst']

@[reassoc (attr := simp)]
lemma baseChangeChartι_snd :
    baseChangeChartι B I ha ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        chartRingι I ha := by
  unfold baseChangeChartι
  rw [Category.assoc, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rfl

lemma opensRange_baseChangeChartι :
    (baseChangeChartι B I ha).opensRange =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) (toSpec I) ⁻¹ᵁ
        (chart I (reesX I a ha) (reesX_mem I a ha)).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [← opensRange_chartRingιOfEq I ha rfl]
  unfold baseChangeChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  simp [Scheme.Pullback.range_map]

/-- The canonical morphism `Bl_{IB}(Spec B) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)`. -/
abbrev baseChangeLift :
    AffineBlowup (I.map (algebraMap A B)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (toSpec I) :=
  pullback.lift (toSpec _) (hom (algebraMap A B) rfl) (hom_toSpec _ rfl).symm

include ha in
lemma algebraMap_mem_map : algebraMap A B a ∈ I.map (algebraMap A B) :=
  Ideal.mem_map_of_mem _ ha

lemma hom_reesX_eq :
    reesGrading.hom (algebraMap A B) rfl (reesX I a ha) =
      reesX (I.map (algebraMap A B)) (algebraMap A B a) (algebraMap_mem_map B I ha) :=
  reesGrading.hom_reesX _ _ _ _

/-- The chart `Spec B[IB/b] ⟶ Bl_{IB}(Spec B)` at the image `b` of `a`, as the chart at the image
of `a·X` under the functoriality of Rees algebras. -/
abbrev baseChangeChartRingι :
    Spec (.of (chartRing (I.map (algebraMap A B)) (algebraMap A B a))) ⟶
      AffineBlowup (I.map (algebraMap A B)) :=
  chartRingιOfEq _ (algebraMap_mem_map B I ha) (hom_reesX_eq B I ha)
    ((reesGrading.hom (algebraMap A B) rfl).map_mem (reesX_mem I a ha))

/-- `θ_b ∘ Away.map = σ_a ∘ (1 ⊗ -) ∘ θ_a` as maps `Away (reesGrading I) (a·X) → B[IB/b]`. -/
lemma homogeneousAwayEquivChartOfEq_awayMap
    (z : HomogeneousLocalization.Away (reesGrading I) (reesX I a ha)) :
    homogeneousAwayEquivChartOfEq _ (algebraMap_mem_map B I ha) (hom_reesX_eq B I ha)
        (HomogeneousLocalization.Away.map (reesGrading.hom (algebraMap A B) rfl)
          (reesX I a ha) z) =
      strictChartMap B I a ha (1 ⊗ₜ homogeneousAwayEquivChart I ha z) := by
  obtain ⟨n, y, hy, h, rfl⟩ := exists_eq_mk I ha z
  apply Subtype.ext
  rw [HomogeneousLocalization.Away.map_mk]
  simp only [reesGrading.hom_reesMonomial]
  rw [coe_homogeneousAwayEquivChartOfEq_mk, coe_strictChartMap, baseChangeChartToAway_tmul,
    map_one, one_mul, homogeneousAwayEquivChart_apply, coe_homogeneousAwayToChart_mk,
    awayBaseChange_chartFraction]

/-- **The blow-up of `Spec B` over the chart at `a`**: the chart of the blow-up of `Spec B` along
`IB` at `b`, the image of `a`, is the preimage of the chart `Spec C_a(A, B, I)` of the base change,
and it maps to `Spec C_a(A, B, I)` by `Spec σ_a`. -/
theorem isPullback_baseChangeChartι :
    IsPullback (Spec.map (CommRingCat.ofHom (strictChartMap B I a ha).toRingHom))
      (baseChangeChartRingι B I ha) (baseChangeChartι B I ha) (baseChangeLift B I) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, chartRingιOfEq_toSpec, Category.assoc,
        baseChangeChartι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact ((strictChartMap B I a ha).comp_algebraMap).symm
    · have key : CommRingCat.ofHom (HomogeneousLocalization.Away.map
            (reesGrading.hom (algebraMap A B) rfl) (reesX I a ha)) ≫
            CommRingCat.ofHom (homogeneousAwayEquivChartOfEq _ (algebraMap_mem_map B I ha)
              (hom_reesX_eq B I ha)).toRingHom =
          CommRingCat.ofHom (homogeneousAwayEquivChartOfEq I ha rfl).toRingHom ≫
            CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
            CommRingCat.ofHom (strictChartMap B I a ha).toRingHom := by
        refine CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_)
        exact homogeneousAwayEquivChartOfEq_awayMap B I ha z
      rw [Category.assoc, pullback.lift_snd, Category.assoc, baseChangeChartι_snd]
      change (Spec.map _ ≫ chart _ _ _) ≫ hom _ _ =
        Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ chart _ _ _
      rw [Category.assoc, chart_hom (algebraMap A B) rfl (reesX I a ha) (reesX_mem I a ha),
        ← Category.assoc, ← Spec.map_comp, key, Spec.map_comp,
        Spec.map_comp]
      simp only [Category.assoc]
  · rw [opensRange_baseChangeChartι, ← Scheme.Hom.comp_preimage, pullback.lift_snd,
      opensRange_chartRingιOfEq, opensRange_chart, opensRange_chart]
    exact Proj.map_preimage_basicOpen (reesGrading.hom (algebraMap A B) rfl)
      (reesGrading.irrelevant_le_map_hom (algebraMap A B) rfl) _

/-- **The strict transform on the chart at `a`**: the kernel of the canonical morphism
`Bl_J(Spec B) ⟶ Spec B ×_{Spec A} Bl_I(Spec A)`, for `J = IB`, restricted to the chart
`Spec C_a(A, B, I)`, is the ideal of the closed subscheme `Spec C_a^st(A, B, I)`. -/
theorem comap_ker_baseChangeChartι {J : Ideal B} (h : I.map (algebraMap A B) = J) :
    (pullback.lift (toSpec J) (hom (algebraMap A B) h) (hom_toSpec _ h).symm :
        AffineBlowup J ⟶ _).ker.comap (baseChangeChartι B I ha) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (baseChangeChartTorsion B I a)))).ker := by
  subst h
  have : IsClosedImmersion (baseChangeLift B I) := isClosedImmersion_pullbackLift _ rfl
  rw [Scheme.Hom.comap_ker_of_isPullback (isPullback_baseChangeChartι B I ha).flip]
  refine Scheme.Hom.ker_specMap_eq_of_ker_eq _ _ ?_
  change RingHom.ker (strictChartMap B I a ha).toRingHom = RingHom.ker (Ideal.Quotient.mk _)
  rw [Ideal.mk_ker]
  exact ker_strictChartMap B I ha

end AffineBlowup

end AlgebraicGeometry
