/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine

/-!
# The trace formula on closed subschemes of a relative affine line

The inductive step of Step 4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`: the trace formula for closed subschemes of the
relative affine line `𝔸¹_{Y₀}` follows from the trace formula for closed subschemes of `Y₀` and
of affine lines over finite fields, by the Weil `!`-pushforward along the projection to `Y₀`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_relativeAffineLine`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {k : Type u} [Field k] [Finite k]

/-- An affine scheme over a finite field `k` has a `#k`-power Frobenius: transport `Spec` of the
`#k`-power map of its ring of global sections along `Y₀ ≅ Spec Γ(Y₀, ⊤)`. -/
lemma _root_.AlgebraicGeometry.exists_isFrobenius_of_isAffine {Y₀ : Scheme.{u}} [IsAffine Y₀]
    (g₀ : Y₀ ⟶ Spec (.of k)) : ∃ F : Y₀ ⟶ Y₀, F.IsFrobenius (Nat.card k) := by
  obtain ⟨φ, hφ, -⟩ := exists_specMap_pow_comp (Y₀.isoSpec.inv ≫ g₀)
  refine ⟨Y₀.isoSpec.hom ≫ Spec.map φ ≫ Y₀.isoSpec.inv, fun R t ψ hψ ↦ ?_⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, Spec.map τ = t ≫ Y₀.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  have hc : φ ≫ τ = τ ≫ ψ := by
    ext r
    simp [hφ, hψ]
  rw [← Category.assoc, ← hτ, ← Category.assoc, ← Spec.map_comp, hc, Spec.map_comp,
    Category.assoc, hτ]
  simp

/-- The inductive step of Step 4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`: let `Y₀` be an affine scheme of finite type over
`k` such that the trace formula holds for all closed subschemes of `Y₀`, and for all closed
subschemes of affine lines over finite fields. Then it holds for all closed subschemes `Z₀` of
the relative affine line `𝔸¹_{Y₀}`: push forward along the projection `Z₀ ⟶ Y₀` with the Weil
`!`-pushforward (`WeilComplex.trace_globalOperator_lowerShriekPush`); its stalk Frobenius at a
fixed point `ȳ` is the degree-one global operator of the fibre over `𝐅_{q^m}`
(`WeilComplex.exists_isModelFrobenius_fibre`), a closed subscheme of the affine line. -/
theorem traceFormulaHolds_of_isClosedImmersion_relativeAffineLine {Y₀ : Scheme.{u}}
    (g₀ : Y₀ ⟶ Spec (.of k)) [IsAffine Y₀] [LocallyOfFiniteType g₀]
    (hY : ∀ {Z₀ : Scheme.{u}} (i : Z₀ ⟶ Y₀) [IsClosedImmersion i], TraceFormulaHolds A (i ≫ g₀))
    (hline : ∀ {k' : Type u} [Field k'] [Finite k'] {Z₀ : Scheme.{u}}
      (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k'))) [IsClosedImmersion i],
      TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k')) ↘ Spec (.of k')))
    {Z₀ : Scheme.{u}} (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Y₀)) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀ ≫ g₀) := by
  intro Ω _ _ G X aX _ _ W σ p hΦ hctf m hm _ _ hX _
  -- (a) the Frobenius of `Y₀` and (b) the base change `Y = Y₀ ×_k Ω`
  obtain ⟨F₀, hF₀, hpF⟩ := hΦ.exists_isFrobenius
  obtain ⟨FY, hFY⟩ := exists_isFrobenius_of_isAffine g₀
  have hYpb := IsPullback.of_hasPullback g₀ σ
  obtain ⟨frobY, hYfrob, hpY⟩ : ∃ frobY : pullback g₀ σ ⟶ pullback g₀ σ,
      frobY ≫ pullback.snd g₀ σ = pullback.snd g₀ σ ∧
        frobY ≫ pullback.fst g₀ σ = pullback.fst g₀ σ ≫ FY :=
    ⟨pullback.lift (pullback.fst g₀ σ ≫ FY) (pullback.snd g₀ σ)
      (by rw [Category.assoc, hFY.comp_eq g₀, pullback.condition]),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  obtain ⟨f, hf, hpf⟩ : ∃ f : X ⟶ pullback g₀ σ, f ≫ pullback.snd g₀ σ = aX ∧
      f ≫ pullback.fst g₀ σ = p ≫ i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀ :=
    ⟨pullback.lift (p ≫ i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀) aX (by simpa using hΦ.isPullback.w),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  have h : f ≫ frobY = W.frobenius ≫ f := comp_eq_comp_of_isPullback hYpb
    (hF₀.comp_eq_comp (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀ ≫ g₀) hFY
      (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀)) W.frobenius_comp hYfrob hpF hpY hpf hf
  -- instances
  have : IsFinite W.frobenius := hF₀.isFinite_of_isPullback hΦ.isPullback W.frobenius_comp hpF
  have : IsFinite frobY := hFY.isFinite_of_isPullback hYpb hYfrob hpY
  have : IsAffine (pullback g₀ σ) := isAffine_of_isAffineHom (pullback.snd g₀ σ)
  have : IsSeparated (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : LocallyOfFiniteType (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : QuasiCompact (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (pullback.snd g₀ σ)
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (pullback.snd g₀ σ)
  have : QuasiCompact f := QuasiCompact.of_comp f (pullback.snd g₀ σ)
  -- (c) the Weil `!`-pushforward and the trace formula on `Y`
  have hL : (W.lowerShriekPush G hctf f hf frobY hYfrob h).IsModelFrobenius g₀ σ
      (pullback.fst g₀ σ) := ⟨hYpb, FY, hFY, hpY⟩
  have hctfL := G.ctf_lowerShriek f (.mk hf) hctf
  have := hL.isFinite_frobeniusIterate _ m
  have : IsProper ((W.lowerShriekPush G hctf f hf frobY hYfrob h).graph G hctfL m).snd :=
    inferInstanceAs
      (IsProper ((W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m))
  let : HasRightDual ((rightDerivedLowerShriek A (pullback.snd g₀ σ)).obj
      (W.lowerShriekPush G hctf f hf frobY hYfrob h).obj) :=
    (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfL).some
  let hLst (y : {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}) :
      HasRightDual (((upperStar A y.1).leftDerivedFunctor).obj
        (W.lowerShriekPush G hctf f hf frobY hYfrob h).obj) :=
    (G.nonempty_hasRightDual_leftDerivedUpperStar_of_comp_eq_id _ hctfL y.1 y.2.1).some
  have := hL.finite_fixedPoints (m := m) (by omega)
  let := Fintype.ofFinite {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}
  have hTFY : TraceFormulaHolds A (𝟙 Y₀ ≫ g₀) := @hY Y₀ (𝟙 Y₀) _
  rw [Category.id_comp] at hTFY
  have hfg := W.frobeniusIterate_comp_eq_comp (W.lowerShriekPush G hctf f hf frobY hYfrob h) f h m
  -- (d) the global operators of `W` and of its pushforward have the same trace
  rw [← W.trace_globalOperator_lowerShriekPush G hctf f hf frobY hYfrob h m,
    hTFY G hL hctfL m hm]
  -- (f) regroup the fixed points of `X` along the fibres
  let hfin (y : {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}) :
      Fintype {x : Spec (.of Ω) ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 _ ∧
        x ≫ (W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1 = x} :=
    Fintype.ofInjective _ (W.fibreFixedPoint_injective f hf m _ hfg y)
  refine Eq.trans ?_ (Fintype.sum_bijective _ (W.bijective_fibreFixedPoint f hf m _ hfg) _ _
    fun _ ↦ rfl)
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  -- (e) the stalk at `ȳ` is the degree-one global operator of the fibre
  obtain ⟨k', _, _, σ', y₀, hy₀, -, hfibM, htr⟩ := WeilComplex.exists_isModelFrobenius_fibre G W
    hctf f hf frobY hYfrob h hΦ hYpb FY hFY hpY (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀)
    (Category.assoc _ _ _) hpf m hm hfg y.1 y.2.1 y.2.2
  have hctfF : G.ctf (pullback f y.1) (W.fibre f m _ hfg y.1 y.2.2).obj :=
    G.ctf_upperStar (pullback.fst f y.1) (.mk (aX := pullback.snd f y.1) (aY := aX)
      (by
        have := pullback.condition_assoc (f := f) (g := y.1) (pullback.snd g₀ σ)
        rwa [hf, y.2.1, Category.comp_id] at this)) hctf
  have := hfibM.isFinite_frobeniusIterate _ 1
  have : IsProper ((W.fibre f m _ hfg y.1 y.2.2).graph G hctfF 1).snd :=
    inferInstanceAs (IsProper ((W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1))
  let : HasRightDual ((rightDerivedLowerShriek A (pullback.snd f y.1)).obj
      (W.fibre f m _ hfg y.1 y.2.2).obj) :=
    (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfF).some
  let hFst (x : {x : Spec (.of Ω) ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 _ ∧
      x ≫ (W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1 = x}) :
      HasRightDual (((upperStar A x.1).leftDerivedFunctor).obj
        (W.fibre f m _ hfg y.1 y.2.2).obj) :=
    let : HasRightDual (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj
        W.obj) := hX (W.fibreFixedPoint f hf m _ hfg y x)
    { rightDual := HasRightDual.rightDual
        (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj W.obj)
      exact := exactPairingCongrLeft
        ((leftDerivedUpperStarComp A x.1 (pullback.fst f y.1)).app W.obj).symm }
  -- the fibre is a closed subscheme of the affine line over `𝐅_{q^m}`
  have hlineF : TraceFormulaHolds A (pullback.snd (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀) y₀) := by
    have e : ((pullbackRightPullbackFstIso (𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀) y₀ i).inv ≫
        pullback.snd i (pullback.fst (𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀) y₀) ≫
        (AffineSpace.isPullback_map (n := PUnit.{u + 1}) y₀).isoPullback.inv) ≫
        𝔸(PUnit.{u + 1}; Spec (.of k')) ↘ Spec (.of k') =
        pullback.snd (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀) y₀ := by
      simp
    rw [← e]
    exact @hline k' _ _ _ _ _
  rw [htr hctfF, hlineF G hfibM hctfF 1 le_rfl]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  let : HasRightDual (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj
      W.obj) := hX (W.fibreFixedPoint f hf m _ hfg y x)
  exact W.trace_stalkFrobenius_fibre f m _ hfg y.1 y.2.2 x.1 x.2.2

end AlgebraicGeometry.ProEtale
