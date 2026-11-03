/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeRealEnvelope
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealMixedByCurves
import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.NativeRelativeEnvelopeFactorReality
import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.NativeHigherShriekConstructible
import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.NativeHigherShriekConstantTwist
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Mixed.NativeMixedSubobjects
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Mixed.NativeMixedConstantTwist

/-!
# Mixedness for a relative affine curve

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-p-dl-general-relative-line/lem-zl-relative-curve-mixedness.md, statement and its proof
(blueprint: lem-zl-relative-curve-mixedness).

The statement is the native condensed-coefficient form of
`lem-zl-relative-curve-mixedness`.  A compactification is the presentation used by
`RelativeCurve.higherShriek`; the conclusion quantifies over every such presentation.

## Main statements

* `WeilConjectures.RelativeCurve.exists_mixed_higherShriek_of_isAffine_fiber`
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace WeilConjectures.RelativeCurve

private def higherShriekFunctor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) (i : ℕ) :
    NativeL2.WeilModule D l U₀ ⥤ NativeL2.WeilModule D l Y₀ :=
  let Λ := Profinite.padicAlgClRingObj.{u} l
  Endofunctor.IsoAlgebra.mapOfNatIso
      ((CondensedRing.upperStar Λ
        (D.geometricFrobenius U₀).hom).mapDerivedCategorySingleFunctor 0) ⋙
    Endofunctor.IsoAlgebra.mapOfNatIso (exchange D l h₀ c₀) ⋙
    Endofunctor.IsoAlgebra.mapOfNatIso
      ((CondensedRing.upperStar Λ
        (D.geometricFrobenius Y₀).hom).mapDerivedCategoryHomologyFunctorIso (i : ℤ))

private theorem higherShriekFunctor_obj
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) (i : ℕ)
    (F : NativeL2.WeilModule D l U₀) :
    (higherShriekFunctor D l h₀ c₀ i).obj F = higherShriek D l h₀ c₀ F i := by
  unfold higherShriek higherShriekFunctor
  rfl

private instance higherShriekFunctor_additive
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) (i : ℕ) :
    (higherShriekFunctor D l h₀ c₀ i).Additive := by
  have : (CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj l) (geometricCompactification D h₀ c₀)).Additive := by
    change ((CondensedRing.openImmersionLowerShriek _ _).mapDerivedCategory ⋙
      (CondensedRing.lowerStar _ _).rightDerivedFunctor).Additive
    infer_instance
  constructor
  intro X Y f g
  apply (Endofunctor.IsoAlgebra.forget _).map_injective
  change (DerivedCategory.homologyFunctor _ (i : ℤ)).map
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) (geometricCompactification D h₀ c₀)).map
        ((DerivedCategory.singleFunctor _ 0).map
          ((Endofunctor.IsoAlgebra.forget _).map (f + g)))) = _
  simp only [Functor.map_add]
  rfl

private theorem higherShriek_isZero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left) (i : ℕ)
    (F : NativeL2.WeilModule D l U₀) (hF : IsZero F) :
    IsZero (higherShriek D l h₀ c₀ F i) := by
  rw [← higherShriekFunctor_obj]
  let := higherShriekFunctor_additive D l h₀ c₀ i
  exact (higherShriekFunctor D l h₀ c₀ i).map_isZero hF

private theorem mixed_of_isZero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀) (hM : IsZero M)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : NativeL2.Mixed D l X₀ M iota w := by
  have hc : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier := by
    have : CompactSpace (D.geometricFiber X₀).left :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    apply ((adicConstructibilityPredicateComparison l (D.geometricFiber X₀).left
      (Profinite.padicAlgClRingObj l) .algebraicClosure).1 M.carrier).mp
    exact isConstructibleModuleObject_of_isZero _
      ((Endofunctor.IsoAlgebra.forget _).map_isZero hM)
  refine ⟨0, fun _ ↦ M, fun i ↦ Fin.elim0 i, fun _ ↦ hc, hM, ⟨Iso.refl M⟩, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- The compactly supported higher direct image of a lisse pure Weil module on a
relative smooth affine curve is mixed with some upper weight in every degree.

The finite-field datum, the prime-away-from-the-characteristic condition, the
separated finite-type hypotheses, smooth relative dimension one, and affine-fibre
condition are the native realization of the geometric hypotheses in the source.
`hAffine` asks the scheme-theoretic fibres to be affine; this is equivalent to the
source's affine nonempty geometric fibres by fpqc descent of affineness along
`Spec κ(y)‾ → Spec κ(y)` [lem-zl-affine-morphism-fpqc-descent] (proof step 2).
`NativeL2.Pure` and `NativeL2.Mixed` render the punctual purity and mixedness
clauses of `def-weil-punctual-weights`; `higherShriek` is the condensed
compact-support operation with its canonical Weil structure.

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-p-dl-general-relative-line/lem-zl-relative-curve-mixedness.md, statement
(blueprint: lem-zl-relative-curve-mixedness).

Proof: (1) If `F = 0` take the empty filtration and `u_i = 0`. Otherwise choose a
closed point of degree `d` with nonzero stalk and a Frobenius eigenvalue `α`; a `d`th
root `b` of `α⁻¹` has `|ι(b)| = q^(-w/2)`. Form `F⁰ = F ⊗ B_b` and
`E = F⁰ ⊕ (F⁰)^∨` [def-wf-normalized-real-envelope]; `F⁰` stays lisse
[lem-wf-condensed-constant-twist-stalk], has weight zero [lem-wf-constant-twist-weight],
so does its dual [lem-tw-dual-negation], and `E` is lisse and real
[lem-wf-envelope-real].
(2) `h` is quasi-compact and smooth of relative dimension one, and its fibres are
affine by [lem-zl-affine-morphism-fpqc-descent]; these are the hypotheses of
[lem-zl-relative-curve-punctual] needed by [lem-zl-relative-envelope-factor-reality],
so `G_i = R^i h_! E` is real. It is constructible [sk-thm-sf-ctf-stability] and carries
the Weil structure of [det-thm-sfb-shriek-base-change, prop-weil-operations].
(3) By [thm-zl-real-mixed-by-curves] `G_i` has a finite mixed filtration with weights at
most some `v_i`. `R^i h_! F⁰` is a Weil-equivariant direct summand of `G_i`
[prop-weil-operations], hence mixed of weights at most `v_i`
[lem-a1-mixed-direct-summand]. Since `F = F⁰ ⊗ h^* B_{b⁻¹}`, the projection formula
[lem-wf-constant-twist-cohomology] and exactness of the twist
[lem-wf-condensed-constant-twist-stalk] give `R^i h_! F ≅ R^i h_! F⁰ ⊗ B_{b⁻¹}`.
Twisting the filtration raises every weight by `w` [lem-wf-constant-twist-weight],
so `u_i = v_i + w` works.
(blueprint: lem-zl-relative-curve-mixedness)
-/
theorem exists_mixed_higherShriek_of_isAffine_fiber
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p)
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (h₀ : U₀ ⟶ Y₀)
    [SmoothOfRelativeDimension 1 h₀.left]
    [IsSeparated h₀.left] [QuasiCompact h₀.left]
    (hAffine : ∀ y : Y₀.left, IsAffine (h₀.left.fiber y))
    (F : NativeL2.WeilModule D l U₀)
    (hLisse : IsLisseCoefficientModule
      (Profinite.padicAlgClRingObj l) F.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hPure : NativeL2.Pure D l U₀ F iota w) :
    ∀ (c₀ : Compactification h₀.left) (i : ℕ), ∃ u_i : ℝ,
      NativeL2.Mixed D l Y₀
        (higherShriek D l h₀ c₀ F i) iota u_i := by
  classical
  by_cases hz : IsZero F
  · intro c₀ i
    exact ⟨0, mixed_of_isZero D l Y₀ _ (higherShriek_isZero D l h₀ c₀ i F hz) iota 0⟩
  · have : IsSeparated U₀.hom := by
      have hsep : IsSeparated (h₀.left ≫ Y₀.hom) := inferInstance
      rwa [h₀.w] at hsep
    have : Nonempty U₀.left := by
      by_contra he
      have : IsEmpty U₀.left := not_nonempty_iff.mp he
      have : IsEmpty (D.geometricFiber U₀).left :=
        ⟨fun x ↦ isEmptyElim ((pullback.fst U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) x)⟩
      have hF := CondensedRing.isZero_mod_of_isEmpty
        (Profinite.padicAlgClRingObj l) F.carrier
      apply hz
      rw [IsZero.iff_id_eq_zero]
      apply (Endofunctor.IsoAlgebra.forget _).map_injective
      simpa using (IsZero.iff_id_eq_zero F.carrier).mp hF
    obtain ⟨b, hb, hpF₀, hreal, hpE, hlisE, ⟨a, r, har⟩, htrace⟩ :=
      NativeEnvelope.exists_normalized_real_envelope D l hl U₀ F iota w hz hLisse hPure
    intro c₀ i
    let E := NativeEnvelope.realEnvelope D l U₀ hl F b
    let F₀ := NativeEnvelope.normalizedTwist D l U₀ hl F b
    let T := higherShriekFunctor D l h₀ c₀ i
    have hcE : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber U₀).left E.carrier := by
      have : CompactSpace (D.geometricFiber U₀).left :=
        QuasiCompact.compactSpace_of_compactSpace
          (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      have : IsLocallyNoetherian (D.geometricFiber U₀).left :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      have : IsNoetherian (D.geometricFiber U₀).left := {}
      exact native_lisse_constructible l _ E.carrier hlisE
    have hcGi := higherShriek_constructible D l hl h₀ c₀ E hcE i
    have hrGi := real_higherShriek_of_isAffine_fiber D l hl h₀ hAffine c₀ E hlisE
      iota hreal hpE i
    obtain ⟨v, hv⟩ := NativeL2.real_isMixed_by_curves D l hl Y₀ hcGi iota hrGi
    have hsplit : T.map a ≫ T.map r = 𝟙 (T.obj F₀) := by
      rw [← T.map_comp, har, T.map_id]
    have : Mono (T.map a) := mono_of_mono_fac hsplit
    have hcF₀ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left (T.obj F₀).carrier := by
      have : CompactSpace (D.geometricFiber U₀).left :=
        QuasiCompact.compactSpace_of_compactSpace
          (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      have : IsLocallyNoetherian (D.geometricFiber U₀).left :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      have : IsNoetherian (D.geometricFiber U₀).left := {}
      have cmp := (adicConstructibilityPredicateComparison l (D.geometricFiber U₀).left
        (Profinite.padicAlgClRingObj l) .algebraicClosure).1
      have hcF := native_lisse_constructible l _ F.carrier hLisse
      have hcF₀' : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (D.geometricFiber U₀).left F₀.carrier :=
        (cmp _).mp (((cmp _).mpr hcF).of_iso (ρ_ F.carrier).symm)
      simpa only [T, higherShriekFunctor_obj] using
        higherShriek_constructible D l hl h₀ c₀ F₀ hcF₀' i
    have hMix : NativeL2.Mixed D l Y₀ (T.obj F₀) iota v :=
      NativeL2.Mixed.of_constructible_mono D l Y₀ (T.map a) hcF₀ iota v (by
        simpa only [T, higherShriekFunctor_obj] using hv)
    let c : ℝ := 2 * Real.logb (Nat.card D.k₀) ‖iota (b⁻¹ : (PadicAlgCl l)ˣ)‖
    have hc : c = w := by
      have hq : (1 : ℝ) < D.q := by
        rw [← D.card_base]
        exact_mod_cast (Finite.one_lt_card (α := D.k₀))
      have hbi : ‖iota (b⁻¹ : (PadicAlgCl l)ˣ)‖ = ‖iota b‖⁻¹ := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv]
      have hb' : ‖iota (b⁻¹ : (PadicAlgCl l)ˣ)‖ = (D.q : ℝ) ^ (w / 2) := by
        rw [hbi, hb, ← Real.rpow_neg (le_of_lt (zero_lt_one.trans hq))]
        congr 1
        ring
      dsimp only [c]
      rw [hb', D.card_base, Real.logb_rpow (zero_lt_one.trans hq) hq.ne']
      ring
    have hTw := NativeL2.Mixed.constantTwist D l hl Y₀ (T.obj F₀) iota v c hMix b⁻¹ rfl
    obtain ⟨eC⟩ := nonempty_higherShriek_normalizedTwist_iso D l hl h₀ c₀ F₀ b⁻¹ i
    obtain ⟨eI⟩ := nonempty_normalizedTwist_inverse_iso D l hl U₀ F b
    let e : NativeEnvelope.normalizedTwist D l Y₀ hl (T.obj F₀) b⁻¹ ≅ T.obj F :=
      (by simpa only [T, higherShriekFunctor_obj] using eC.symm) ≪≫ T.mapIso eI
    refine ⟨v + w, ?_⟩
    simpa only [hc, T, higherShriekFunctor_obj] using
      NativeL2.Mixed.of_iso D l Y₀ e iota (v + c) hTw

end WeilConjectures.RelativeCurve
