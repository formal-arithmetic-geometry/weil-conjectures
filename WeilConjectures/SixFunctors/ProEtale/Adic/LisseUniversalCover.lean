/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CocycleLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Descent
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Trivialization
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection

/-!
# Lisse sheaves are constant on the universal profinite étale cover

Let `Y` be a connected regular Noetherian scheme and `Ỹ_y` its universal profinite étale cover
at a geometric point `y` (`AlgebraicGeometry.Scheme.UniversalCovers`). Every lisse `ℓ`-adic sheaf
`G` on `Y_proét` becomes constant on `Ỹ_y`: `G|_{Ỹ_y} ≅ ℚ̄_ℓⁿ`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_upperStar_universalCover`).

This is the `ℚ̄_ℓ`-part of the blueprint `cor-galois-lisse-representations` in the form needed
here. The blueprint deduces it from the case of finite coefficients by passing to the
coefficient stages; in the Bhatt–Scholze model of lisse sheaves used in this project
(pro-étale locally free `ℚ̄_ℓ,Y`-modules, whose sections are *locally finite* continuous
`ℚ̄_ℓ`-valued functions) we argue with the descent data of a trivialisation instead, following
Bhatt–Scholze (*The pro-étale topology for schemes*, §7.4):

1. `G` is trivialised on a single affine pro-étale cover `f : V ⟶ Y`, `f^* G ≅ ℚ̄_ℓⁿ`
   (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_affine_cover_iso`); its transition
   matrix on the compact `V ×_Y V` takes values in `GL_n(E)` for a finite extension `E` of
   `ℚ_ℓ` (`PadicAlgCl.exists_finiteDimensional_forall_mem`), and is a cocycle `γ`
   (`AlgebraicGeometry.ProEtale.AdicSheaf.transitionMatrix_trans`,
   `AlgebraicGeometry.ProEtale.AdicSheaf.transitionMatrix_comp`).
2. For every congruence subgroup `K_k ⊆ GL_n(𝒪_E)` (`PadicAlgCl.congruenceSubgroup`), `γ`
   twists the discrete set `GL_n(E) ⧸ K_k` into a pro-étale locally constant sheaf of sets on
   `Y`, which is constant on `Ỹ_y` (`AlgebraicGeometry.exists_isTwistedSection_universalCover`,
   Bhatt–Scholze, Lemma 7.4.10). For `k = 0` this is the existence of an `𝒪_E`-lattice, and for
   `k ≥ 1` the triviality on `Ỹ_y` of its reductions modulo `ℓᵏ`.
3. Sections over the connected `Ỹ_y` are determined by one value
   (`AlgebraicGeometry.IsTwistedSection.apply_eq_of_preconnectedSpace`); König's lemma and the
   completeness of `GL_n(E)` give a trivialisation of `γ` over `V ×_Y Ỹ_y`
   (`CocycleTrivialization.exists_cocycle_trivialization`).
4. Correcting the pulled back trivialisation by it, the descent datum becomes trivial and the
   trivialisation descends to `Ỹ_y`
   (`AlgebraicGeometry.ProEtale.AdicSheaf.nonempty_iso_of_transitionMatrix_eq_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

open PadicAlgCl AdicSheaf

/-- Two matrices of locally finite functions agreeing at every point are equal. -/
lemma matrix_ext_eval {T : Type*} [TopologicalSpace T] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T)}
    (h : ∀ t, A.map (locallyFiniteFunctionsEval t) = B.map (locallyFiniteFunctionsEval t)) :
    A = B :=
  Matrix.ext fun i j ↦ Subtype.ext (ContinuousMap.ext fun t ↦ congrFun (congrFun (h t) i) j)

/-- **Lisse sheaves are constant on the universal cover** (blueprint:
`cor-galois-lisse-representations`, the case `Λ = ℚ̄_ℓ`). On a connected regular Noetherian
scheme `Y`, the pullback of a lisse `ℓ`-adic sheaf to the universal profinite étale cover `Ỹ_y`
at a geometric point `y` is isomorphic to `ℚ̄_ℓⁿ` for some `n`. -/
theorem IsAdicLisseSheaf.exists_iso_upperStar_universalCover [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G : AdicSheaf l Y} (hG : IsAdicLisseSheaf G) :
    ∃ n : ℕ, Nonempty ((U.proj y)^*ᵃ[l].obj G ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)) := by
  classical
  -- 1. a single affine trivialising cover
  obtain ⟨V, f, hfe, hfs, hfq, hV, n, ⟨e⟩⟩ := hG.exists_affine_cover_iso (l := l)
  refine ⟨n, ?_⟩
  set π := U.proj y
  have := U.weaklyEtale_proj y
  have := U.connectedSpace y
  -- the transition matrices on `V ×_Y V`
  let g := transitionMatrix e (pullback.fst f f) (pullback.snd f f) pullback.condition
  let g' := transitionMatrix e (pullback.snd f f) (pullback.fst f f) pullback.condition.symm
  have hgg' : g * g' = 1 := by
    rw [← transitionMatrix_trans]
    exact transitionMatrix_self _ _ _
  have hg'g : g' * g = 1 := by
    rw [← transitionMatrix_trans]
    exact transitionMatrix_self _ _ _
  -- a finite extension `E` containing their values
  obtain ⟨E, hE, hEmem⟩ := exists_finiteDimensional_forall_mem (l := l) (T := pullback f f)
    ((Finset.univ.image fun p : Fin n × Fin n ↦ g p.1 p.2) ∪
      Finset.univ.image fun p : Fin n × Fin n ↦ g' p.1 p.2)
  have hgE (i j : Fin n) (z) : (g i j).1 z ∈ E :=
    hEmem _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) z
  have hg'E (i j : Fin n) (z) : (g' i j).1 z ∈ E :=
    hEmem _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) z
  -- the cocycle `γ = g⁻¹ : V ×_Y V → GL_n(E)`
  let γ : pullback f f → GL (Fin n) E := glOfMatrix g' g hg'g hgg' hg'E hgE
  have hγc (i j : Fin n) := continuous_glOfMatrix_apply g' g hg'g hgg' hg'E hgE i j
  have hγdiag (v : V) : γ ((pullback.diagonal f).base v) = 1 := by
    sorry
  have hγcocycle (w : tripleProduct f) : γ ((tripleProj₁₃ f).base w) =
      γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
        γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) := by
    sorry
  have hcoc (k : ℕ) : IsDescentCocycle f
      (fun z (s : GL (Fin n) E ⧸ congruenceSubgroup E n k) ↦ γ z • s) where
    isLocallyConstant s := isLocallyConstant_smul_mk γ (fun i j ↦ (hγc i j).1)
      (fun i j ↦ (hγc i j).2) k s
    bijective z := MulAction.bijective (γ z)
    diagonal v := funext fun s ↦ by simp [hγdiag v]
    cocycle w := funext fun s ↦ by simp [hγcocycle w, mul_smul]
  -- 2.–3. the cocycle is trivial over `V ×_Y Ỹ_y`
  obtain ⟨σ, hσlc, hσ⟩ := CocycleTrivialization.exists_cocycle_trivialization
    (p₁ := (pullback.fst (pullback.snd f π) (pullback.snd f π)).base)
    (p₂ := (pullback.snd (pullback.snd f π) (pullback.snd f π)).base)
    (g := fun w ↦ γ ((twistedPairMap f π).base w)) (congruenceSubgroup E n)
    (fun k ↦ congruenceSubgroup_antitone k.le_succ) finite_image_congruenceSubgroup_zero
    exists_limit_congruenceSubgroup (fun _ ↦ eq_one_of_forall_mem_congruenceSubgroup)
    (fun τ hτ hinv x x' ↦ IsTwistedSection.apply_eq_of_preconnectedSpace π τ hτ hinv x x')
    (fun k x ↦ exists_isTwistedSection_universalCover U y f (hcoc k) x _)
  have hσc (i j : Fin n) := continuous_apply_of_isLocallyConstant_mk σ hσlc i j
  -- 4. the corrected trivialisation over `V ×_Y Ỹ_y` descends
  let H := matrixOfGL (fun x ↦ (σ x)⁻¹) fun i j ↦ (hσc i j).2
  let H' := matrixOfGL σ fun i j ↦ (hσc i j).1
  have hHH' : H * H' = 1 := matrixOfGL_mul _ _ _ _ fun x ↦ inv_mul_cancel (σ x)
  have hH'H : H' * H = 1 := matrixOfGL_mul _ _ _ _ fun x ↦ mul_inv_cancel (σ x)
  have : IsIso (ofUnitMatrix H) := isIso_ofUnitMatrix H (Matrix.isUnit_det_of_right_inverse hHH')
  let εT := trivBaseChange e π (pullback.snd f π) (pullback.fst f π) pullback.condition ≪≫
    asIso (ofUnitMatrix H)
  refine nonempty_iso_of_transitionMatrix_eq_one (pullback.snd f π) εT ?_
  sorry

end AlgebraicGeometry.ProEtale
