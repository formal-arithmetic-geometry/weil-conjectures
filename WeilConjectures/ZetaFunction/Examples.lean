/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnected
public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.Curve
public import WeilConjectures.WeilSheaf.TraceIsomorphism
public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Examples of zeta functions and of compactly supported cohomology

This file works out the basic examples of the blueprint chapter on zeta functions and the Weil
conjectures, over a finite field `k` with `q` elements.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.zetaSeries_mul_eq_of_pointCount_eq`: if the point counts are
  `N_n = d₀ a₀ⁿ - d₁ a₁ⁿ + d₂ a₂ⁿ`, then
  `Z(T) (1 - a₀ T)^{d₀} (1 - a₂ T)^{d₂} = (1 - a₁ T)^{d₁}`.
- `AlgebraicGeometry.Scheme.finiteFieldZeta` (`ex-weil-finite-field-zeta`): `Spec k` has
  `N_n = 1`, `Z = (1 - T)⁻¹` and a single closed point, of degree one.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- If the point counts of `X` over `k` are `N_n = d₀ a₀ⁿ - d₁ a₁ⁿ + d₂ a₂ⁿ` for all `n ≥ 1`,
then `Z(X, T) (1 - a₀ T)^{d₀} (1 - a₂ T)^{d₂} = (1 - a₁ T)^{d₁}`. This is the cohomological
determinant factorisation `TraceDatum.zeta_mul_prod_even_eq_prod_odd` for the trace datum of the
homotheties `aᵢ` on `ℚ^{dᵢ}`. -/
theorem Hom.zetaSeries_mul_eq_of_pointCount_eq (f : X.Hom (Spec (.of k))) (d₀ d₁ d₂ : ℕ)
    (a₀ a₁ a₂ : ℚ)
    (h : ∀ n, 1 ≤ n → (f.pointCount n : ℚ) = d₀ * a₀ ^ n - d₁ * a₁ ^ n + d₂ * a₂ ^ n) :
    f.zetaSeries * ((1 - PowerSeries.C a₀ * PowerSeries.X) ^ d₀ *
        (1 - PowerSeries.C a₂ * PowerSeries.X) ^ d₂) =
      (1 - PowerSeries.C a₁ * PowerSeries.X) ^ d₁ := by
  let d : Fin 3 → ℕ := ![d₀, d₁, d₂]
  let a : Fin 3 → ℚ := ![a₀, a₁, a₂]
  let D : TraceDatum.{0, 0} ℚ 2 :=
    { V := fun i ↦ Fin (d i) → ℚ
      F := fun i ↦ a i • 1
      N := fun n ↦ f.pointCount n
      trace_eq := fun n hn ↦ by
        simp only [Int.cast_natCast, h n hn, smul_pow, one_pow, map_smul, LinearMap.trace_one,
          Module.finrank_fin_fun, smul_eq_mul, d, a]
        rw [Fin.sum_univ_three]
        simp
        ring }
  have hP : ∀ i, (D.P i : PowerSeries ℚ) = (1 - PowerSeries.C (a i) * PowerSeries.X) ^ d i :=
    fun i ↦ by
      rw [D.P_def]
      change (((a i • 1 : Module.End ℚ (Fin (d i) → ℚ)).charpolyRev : Polynomial ℚ) :
        PowerSeries ℚ) = _
      rw [LinearMap.charpolyRev_smul_one, Module.finrank_fin_fun]
      simp
  have hz : f.zetaSeries = D.zeta := by
    rw [← D.map_zetaSeries f (fun n ↦ rfl), Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have key := D.zeta_mul_prod_even_eq_prod_odd
  have he : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Even (i : ℕ)) = {0, 2} := by decide
  have ho : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Odd (i : ℕ)) = {1} := by decide
  rw [he, ho, Finset.prod_pair (by decide), Finset.prod_singleton, hP, hP, hP, ← hz] at key
  exact key

/-- Blueprint `ex-weil-finite-field-zeta` (finite-field zeta normalization), point counts: the
scheme `Y₀ = Spec k` over itself has exactly one point over every finite extension of `k`, so
`N_n(Y₀) = 1`. -/
theorem pointCount_id_spec (n : ℕ) : Hom.pointCount (𝟙 (Spec (.of k))) n = 1 := by
  rw [Hom.pointCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun g g' ↦ Subtype.ext ?_⟩, ⟨⟨Spec.map (CommRingCat.ofHom (algebraMap k _)), ?_⟩⟩⟩
  · rw [← Category.comp_id g.1, ← Category.comp_id g'.1, g.2, g'.2]
  · exact Category.comp_id _

/-- Blueprint `ex-weil-finite-field-zeta` (finite-field zeta normalization), zeta function: the
zeta function of `Y₀ = Spec k` over itself is `Z(Y₀, T) = (1 - T)⁻¹`. -/
theorem zetaSeries_id_spec [Finite k] :
    Hom.zetaSeries (𝟙 (Spec (.of k))) * (1 - PowerSeries.X) = 1 := by
  have h := Hom.zetaSeries_mul_eq_of_pointCount_eq (𝟙 (Spec (.of k))) 1 0 0 1 0 0
    fun n _ ↦ by simp [pointCount_id_spec]
  simpa using h

/-- Blueprint `ex-weil-finite-field-zeta` (finite-field zeta normalization), closed points: the
scheme `Y₀ = Spec k` has exactly one closed point (point with finite residue field), and it has
degree one over `k`. -/
theorem finitePoints_spec [Finite k] :
    Nat.card (Spec (.of k)).finitePoints = 1 ∧
      ∀ x : Spec (.of k), Hom.degreeOver (𝟙 (Spec (.of k))) x = 1 := by
  refine ⟨?_, fun x ↦ Hom.degreeOver_eq_one_of_comp_eq_id (𝟙 (Spec (.of k))) (𝟙 _)
    (Category.id_comp _) x⟩
  have hx : ∀ x : Spec (.of k), x ∈ (Spec (.of k)).finitePoints := fun x ↦
    Hom.mem_finitePoints_of_comp_eq_id (𝟙 (Spec (.of k))) (𝟙 _) (Category.id_comp _) x
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y ↦ Subtype.ext (Subsingleton.elim (α := PrimeSpectrum k) _ _)⟩,
    ⟨⟨IsLocalRing.closedPoint k, hx _⟩⟩⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

section PointCounts

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- The `K`-point `t = c` of the affine line `𝔸¹_k`, for a field extension `K` of `k`. -/
def affineLinePoint (c : K) : Spec (.of K) ⟶ affineLine k :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    fun _ ↦ (Scheme.ΓSpecIso (.of K)).inv c

@[reassoc (attr := simp)]
lemma affineLinePoint_over (c : K) :
    affineLinePoint k c ≫ affineLine k ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  AffineSpace.homOfVector_over _ _

@[simp]
lemma affineLinePoint_appTop_coord (c : K) :
    (affineLinePoint k c).appTop (AffineSpace.coord _ PUnit.unit) =
      (Scheme.ΓSpecIso (.of K)).inv c :=
  AffineSpace.homOfVector_appTop_coord _ _ _

variable (K) in
/-- The `K`-rational points of the affine line `𝔸¹_k` are the elements of `K`: a `k`-morphism
`Spec K ⟶ 𝔸¹_k` is determined by the value of the coordinate `t`. -/
def affineLineFieldPointsEquiv : (affineLine k ↘ Spec (.of k)).fieldPoints K ≃ K where
  toFun g := (Scheme.ΓSpecIso (.of K)).hom (g.1.appTop (AffineSpace.coord _ PUnit.unit))
  invFun c := ⟨affineLinePoint k c, affineLinePoint_over k c⟩
  left_inv g := Subtype.ext <| AffineSpace.hom_ext (by rw [affineLinePoint_over, g.2])
    fun ⟨⟩ ↦ by rw [affineLinePoint_appTop_coord, Iso.hom_inv_id_apply]
  right_inv c := by
    simp only [affineLinePoint_appTop_coord]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c

lemma affineLineFieldPointsEquiv_symm_apply (c : K) :
    ((affineLineFieldPointsEquiv k K).symm c).1 = affineLinePoint k c :=
  rfl

/-- The `K`-point `t = c` of `𝔸¹_k` lies in the locus `D(t)` if and only if `c ≠ 0`. -/
lemma affineLinePoint_mem_basicOpen_iff (c : K) (x : Spec (.of K)) :
    (affineLinePoint k c).base x ∈
        (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) ↔ c ≠ 0 := by
  change x ∈ affineLinePoint k c ⁻¹ᵁ
    (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) ↔ _
  rw [Scheme.preimage_basicOpen_top, affineLinePoint_appTop_coord, basicOpen_eq_of_affine,
    PrimeSpectrum.mem_basicOpen, Ideal.eq_bot_of_prime x.asIdeal, Ideal.mem_bot]

/-- **Point count of the affine line** (blueprint `ex-weil-affine-line`):
`#𝔸¹(𝔽_{qⁿ}) = qⁿ` for `n ≥ 1`. -/
theorem pointCount_affineLine [Finite k] {n : ℕ} (hn : n ≠ 0) :
    (affineLine k ↘ Spec (.of k)).pointCount n = Nat.card k ^ n :=
  (Nat.card_congr (affineLineFieldPointsEquiv k _)).trans
    (FiniteField.nat_card_galoisExtension k n hn)

/-- The multiplicative group `𝔾_{m,k}`, realised as the open subscheme `D(t) ⊆ 𝔸¹_k` where the
coordinate `t` is invertible, i.e. `Spec k[t, t⁻¹]`. -/
abbrev multiplicativeGroup : Scheme.{u} :=
  (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- `𝔾_{m,k}` is a `k`-scheme via `D(t) ⊆ 𝔸¹_k ⟶ Spec k`. -/
instance : (multiplicativeGroup k).Over (Spec (.of k)) :=
  ⟨Scheme.Opens.ι _ ≫ affineLine k ↘ Spec (.of k)⟩

lemma multiplicativeGroup_over :
    multiplicativeGroup k ↘ Spec (.of k) = Scheme.Opens.ι _ ≫ affineLine k ↘ Spec (.of k) :=
  rfl

variable (K) in
/-- The `K`-rational points of `𝔾_{m,k}` are the nonzero elements of `K`. -/
def multiplicativeGroupFieldPointsEquiv :
    (multiplicativeGroup k ↘ Spec (.of k)).fieldPoints K ≃ {c : K // c ≠ 0} where
  toFun g := ⟨affineLineFieldPointsEquiv k K ⟨g.1 ≫ Scheme.Opens.ι _, by
      rw [Category.assoc]; exact g.2⟩, by
    set c := affineLineFieldPointsEquiv k K ⟨g.1 ≫ Scheme.Opens.ι _, by
      rw [Category.assoc]; exact g.2⟩
    have hc : affineLinePoint k c = g.1 ≫ Scheme.Opens.ι _ :=
      congrArg Subtype.val ((affineLineFieldPointsEquiv k K).symm_apply_apply _)
    rw [← affineLinePoint_mem_basicOpen_iff k c (IsLocalRing.closedPoint K), hc]
    exact (g.1.base (IsLocalRing.closedPoint K)).2⟩
  invFun c := ⟨IsOpenImmersion.lift (Scheme.Opens.ι _) (affineLinePoint k c.1) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (affineLinePoint_mem_basicOpen_iff k c.1 x).2 c.2), by
    rw [multiplicativeGroup_over, IsOpenImmersion.lift_fac_assoc, affineLinePoint_over]⟩
  left_inv g := Subtype.ext <| (cancel_mono (Scheme.Opens.ι _)).1 <| by
    rw [IsOpenImmersion.lift_fac]
    exact congrArg Subtype.val ((affineLineFieldPointsEquiv k K).symm_apply_apply _)
  right_inv c := Subtype.ext <| by
    simp only [IsOpenImmersion.lift_fac]
    exact (affineLineFieldPointsEquiv k K).apply_symm_apply c.1

/-- **Point count of the multiplicative group** (blueprint `ex-weil-multiplicative-group`):
`#𝔾_m(𝔽_{qⁿ}) = qⁿ - 1` for `n ≥ 1`. -/
theorem pointCount_multiplicativeGroup [Finite k] {n : ℕ} (hn : n ≠ 0) :
    (multiplicativeGroup k ↘ Spec (.of k)).pointCount n = Nat.card k ^ n - 1 := by
  rw [Scheme.Hom.pointCount, Nat.card_congr (multiplicativeGroupFieldPointsEquiv k _),
    ← Nat.card_congr unitsEquivNeZero, Nat.card_units,
    FiniteField.nat_card_galoisExtension k n hn]

end PointCounts

end AlgebraicGeometry

namespace AlgebraicGeometry

section ProjectiveLine

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- The `K`-point `t = 0` of `𝔸¹_k` is the composite of `Spec K ⟶ Spec k` with the zero
section. -/
lemma affineLinePoint_zero :
    affineLinePoint k (0 : K) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ AffineSpace.zeroSection _ _ :=
  AffineSpace.hom_ext (by simp) fun ⟨⟩ ↦ by
    rw [affineLinePoint_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.zeroSection_appTop_coord, map_zero, map_zero]

variable (K) in
/-- The `K`-rational points of `ℙ¹_k` as `K ⊔ {∞}`: `some c` is the point `t = c` of the affine
chart and `none` is the point at infinity. -/
def projectiveLineFieldPoint :
    Option K → (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).fieldPoints K
  | some c => ⟨affineLinePoint k c ≫ ProjectiveLine.affineChart _, by
      rw [Category.assoc, ProjectiveLine.affineChart_over, affineLinePoint_over]⟩
  | none => ⟨Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ ProjectiveLine.infinity _, by
      rw [Category.assoc, ProjectiveLine.infinity_over, Category.comp_id]⟩

lemma projectiveLineFieldPoint_bijective :
    Function.Bijective (projectiveLineFieldPoint k K) := by
  have hinf : ∀ x : Spec (.of K),
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ ProjectiveLine.infinity _).base x ∉
        (ProjectiveLine.affineChart (Spec (.of k))).opensRange := fun x ↦ by
    have h : (ProjectiveLine.infinity (Spec (.of k))).base
        ((Spec.map (CommRingCat.ofHom (algebraMap k K))).base x) ∈
        Set.range (ProjectiveLine.infinity (Spec (.of k))).base := ⟨_, rfl⟩
    rw [ProjectiveLine.range_infinity] at h
    exact h
  have haff : ∀ (c : K) (x : Spec (.of K)),
      (affineLinePoint k c ≫ ProjectiveLine.affineChart _).base x ∈
        (ProjectiveLine.affineChart (Spec (.of k))).opensRange := fun c x ↦
    ⟨(affineLinePoint k c).base x, rfl⟩
  set x₀ : Spec (.of K) := IsLocalRing.closedPoint K
  refine ⟨fun a b hab ↦ ?_, fun g ↦ ?_⟩
  · have hab' := congrArg Subtype.val hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · change Spec.map _ ≫ ProjectiveLine.infinity _ = affineLinePoint k b ≫ _ at hab'
      exact (hinf x₀ (by rw [hab']; exact haff b x₀)).elim
    · change affineLinePoint k a ≫ _ = Spec.map _ ≫ ProjectiveLine.infinity _ at hab'
      exact (hinf x₀ (by rw [← hab']; exact haff a x₀)).elim
    · have h := (cancel_mono (ProjectiveLine.affineChart _)).1 hab'
      have := congrArg (affineLineFieldPointsEquiv k K)
        (Subtype.ext h : (affineLineFieldPointsEquiv k K).symm a =
          (affineLineFieldPointsEquiv k K).symm b)
      simp only [Equiv.apply_symm_apply] at this
      rw [this]
  · have hsub : ∀ x : Spec (.of K), x = x₀ := fun x ↦ Subsingleton.elim (α := PrimeSpectrum K) _ _
    by_cases hx : g.1.base x₀ ∈ (ProjectiveLine.affineChart (Spec (.of k))).opensRange
    · have hr :
          Set.range g.1.base ⊆ Set.range (ProjectiveLine.affineChart (Spec (.of k))).base := by
        rintro _ ⟨x, rfl⟩
        rw [hsub x]
        exact hx
      set h := IsOpenImmersion.lift (ProjectiveLine.affineChart _) g.1 hr
      have hh :
          h ≫ affineLine k ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
        rw [← ProjectiveLine.affineChart_over, ← Category.assoc, IsOpenImmersion.lift_fac, g.2]
      refine ⟨some (affineLineFieldPointsEquiv k K ⟨h, hh⟩), Subtype.ext ?_⟩
      change ((affineLineFieldPointsEquiv k K).symm _).1 ≫ _ = _
      rw [Equiv.symm_apply_apply, IsOpenImmersion.lift_fac]
    · have hx' : g.1.base x₀ ∈ (ProjectiveLine.infinityChart (Spec (.of k))).opensRange := by
        have : g.1.base x₀ ∈ (ProjectiveLine.affineChart (Spec (.of k))).opensRange ⊔
            (ProjectiveLine.infinityChart (Spec (.of k))).opensRange := by
          rw [ProjectiveLine.opensRange_affineChart_sup_opensRange_infinityChart]
          trivial
        exact this.resolve_left hx
      have hr : Set.range g.1.base ⊆
          Set.range (ProjectiveLine.infinityChart (Spec (.of k))).base := by
        rintro _ ⟨x, rfl⟩
        rw [hsub x]
        exact hx'
      set h := IsOpenImmersion.lift (ProjectiveLine.infinityChart _) g.1 hr
      have hh :
          h ≫ affineLine k ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
        rw [← ProjectiveLine.infinityChart_over, ← Category.assoc, IsOpenImmersion.lift_fac, g.2]
      set c := affineLineFieldPointsEquiv k K ⟨h, hh⟩
      have hc : affineLinePoint k c = h :=
        congrArg Subtype.val ((affineLineFieldPointsEquiv k K).symm_apply_apply _)
      have hc0 : c = 0 := by
        by_contra hne
        have hmem := (affineLinePoint_mem_basicOpen_iff k c x₀).2 hne
        rw [← ProjectiveLine.infinityChart_preimage_opensRange_affineChart, hc] at hmem
        apply hx
        have hmem' : (h ≫ ProjectiveLine.infinityChart _).base x₀ ∈
            (ProjectiveLine.affineChart (Spec (.of k))).opensRange := hmem
        rwa [IsOpenImmersion.lift_fac] at hmem'
      have hg : g.1 = h ≫ ProjectiveLine.infinityChart _ := (IsOpenImmersion.lift_fac _ _ _).symm
      refine ⟨none, Subtype.ext ?_⟩
      change _ ≫ ProjectiveLine.infinity _ = g.1
      rw [hg, ← hc, hc0, affineLinePoint_zero, ProjectiveLine.infinity, Category.assoc]

/-- **Point count of the projective line** (blueprint `ex-weil-projective-line-endpoints`):
`#ℙ¹(𝔽_{qⁿ}) = 1 + qⁿ` for `n ≥ 1`. -/
theorem pointCount_projectiveLine [Finite k] {n : ℕ} (hn : n ≠ 0) :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).pointCount n = 1 + Nat.card k ^ n := by
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  rw [Scheme.Hom.pointCount, ← Nat.card_eq_of_bijective _ (projectiveLineFieldPoint_bijective k),
    Nat.card_congr (Equiv.optionEquivSumPUnit.{0} _), Nat.card_sum,
    FiniteField.nat_card_galoisExtension k n hn, Nat.card_unique (α := PUnit.{1}), add_comm]

end ProjectiveLine

end AlgebraicGeometry

namespace AlgebraicGeometry

section Zeta

variable (k : Type u) [Field k] [Finite k]

/-- **Zeta function of the affine line** (blueprint `ex-weil-affine-line`):
`Z(𝔸¹, T) = (1 - qT)⁻¹`. -/
theorem zetaSeries_affineLine :
    (affineLine k ↘ Spec (.of k)).zetaSeries *
      (1 - PowerSeries.C (Nat.card k : ℚ) * PowerSeries.X) = 1 := by
  have h := Scheme.Hom.zetaSeries_mul_eq_of_pointCount_eq (affineLine k ↘ Spec (.of k)) 0 0 1
    0 0 (Nat.card k) fun n hn ↦ by
      rw [pointCount_affineLine k (by omega)]
      push_cast
      ring
  simpa using h

/-- **Zeta function of the multiplicative group** (blueprint `ex-weil-multiplicative-group`):
`Z(𝔾_m, T) = (1 - T) / (1 - qT)`. -/
theorem zetaSeries_multiplicativeGroup :
    (multiplicativeGroup k ↘ Spec (.of k)).zetaSeries *
      (1 - PowerSeries.C (Nat.card k : ℚ) * PowerSeries.X) = 1 - PowerSeries.X := by
  have h := Scheme.Hom.zetaSeries_mul_eq_of_pointCount_eq (multiplicativeGroup k ↘ Spec (.of k))
    0 1 1 0 1 (Nat.card k) fun n hn ↦ by
      rw [pointCount_multiplicativeGroup k (by omega),
        Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos)]
      push_cast
      ring
  simpa using h

/-- **Zeta function of the projective line** (blueprint `ex-weil-projective-line-endpoints`):
`Z(ℙ¹, T) = ((1 - T)(1 - qT))⁻¹`. -/
theorem zetaSeries_projectiveLine :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).zetaSeries *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℚ) * PowerSeries.X)) = 1 := by
  have h := Scheme.Hom.zetaSeries_mul_eq_of_pointCount_eq
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) 1 0 1 1 0 (Nat.card k) fun n hn ↦ by
      rw [pointCount_projectiveLine k (by omega)]
      push_cast
      ring
  simpa using h

end Zeta

end AlgebraicGeometry

end
