/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.LocalDerivation
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections

/-!
# The canonical sheaf of the projective line

Let `k` be a field and `ℙ¹_k = ProjectiveLine (Spec k)`, covered by the standard opens
`U₀ = D₊(x₀)` and `U₁ = D₊(x₁)` with coordinates `t = x₁ / x₀` and `s = x₀ / x₁`. We show
`Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`.

The sheaf of differentials has no local description in this library yet; we only use its
universal property. The derivation `d / dt` of `Γ(U₀) = k[t]`, with values in `𝒪(-2)` through
its generator `x₀⁻²` over `U₀`, and `-d / ds` on `U₁`, extend to local derivations over the
affine opens `U₀` and `U₁` (`AlgebraicGeometry.Scheme.Modules.LocalDerivation.ofIsAffineOpen`),
agree on `U₀ ∩ U₁` by the chain rule, and glue to a derivation `𝒪 → 𝒪(-2)`, that is a morphism
`Ω¹ ⟶ 𝒪(-2)`. Conversely the generators `x₀⁻²` and `x₁⁻²` of `𝒪(-2)` go to `dt` and `-ds`,
which satisfy the same transition rule `dt = -t² ds` (`x₀⁻² = t² x₁⁻²`). Both composites are the
identity, as two derivations agreeing on the coordinates agree.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R] {s : Set n}

/-- The product of two Laurent monomials is the Laurent monomial of the sum of the exponents. -/
lemma awayMonomial_mul (e e' e'' : laurentExponents s 0) (h : e''.1 = e.1 + e'.1) :
    awayMonomial R s e * awayMonomial R s e' = awayMonomial R s e'' := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have ha' := add_nsmul_indicator_nonneg e'.2.2 (neg_le_negExponentSum e'.1)
  have ha'' := add_nsmul_indicator_nonneg e''.2.2 (neg_le_negExponentSum e''.1)
  rw [HomogeneousLocalization.val_mul, awayMonomial, awayMonomial, awayMonomial, Away.val_mk,
    Away.val_mk, Away.val_mk, Localization.mk_mul]
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha')
    (add_nonneg (nsmul_nonneg h0 (negExponentSum e.1)) (nsmul_nonneg h0 (negExponentSum e'.1)))
    ha'' (nsmul_nonneg h0 (negExponentSum e''.1)) (monomialToNat_mul ha ha') ?_ rfl ?_ ?_
  · simp only [Submonoid.coe_mul, monomialToNat_pow h0]
    exact monomialToNat_mul (nsmul_nonneg h0 _) (nsmul_nonneg h0 _)
  · simp only [monomialToNat_pow h0]
  · rw [h]
    abel

/-- The Laurent monomial with exponent `0` is `1`. -/
lemma awayMonomial_zero (e : laurentExponents s 0) (h : e.1 = 0) : awayMonomial R s e = 1 := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  rw [HomogeneousLocalization.val_one, awayMonomial, Away.val_mk, ← Localization.mk_one]
  refine mk_eq_mk_of_monomialToNat (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0 (negExponentSum e.1)) le_rfl le_rfl rfl ?_ monomialToNat_zero.symm
    monomialToNat_zero.symm ?_
  · simp only [monomialToNat_pow h0]
  · rw [h]
    simp

/-- The `m`-th power of a Laurent monomial is the Laurent monomial of `m` times the exponent. -/
lemma awayMonomial_pow (e : laurentExponents s 0) (m : ℕ) (e' : laurentExponents s 0)
    (h : e'.1 = m • e.1) : awayMonomial R s e' = awayMonomial R s e ^ m := by
  induction m generalizing e' with
  | zero => exact (awayMonomial_zero (R := R) e' (by simpa using h)).trans (pow_zero _).symm
  | succ m ih =>
    let e₀ : laurentExponents s 0 := ⟨m • e.1, by
      simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, e.2.1, mul_zero], fun i hi ↦
      nsmul_nonneg (e.2.2 i hi) m⟩
    rw [pow_succ, ← ih e₀ rfl, awayMonomial_mul e₀ e e' (by rw [h, succ_nsmul])]

/-- The function `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the function `xᵉ` on the smaller open
`D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma presheaf_map_awayToSection_awayMonomial {t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (Proj (homogeneousSubmodule n R)).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (Proj.awayToSection _ _ (awayMonomial R t e)) =
      Proj.awayToSection _ _ (awayMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  change ((Proj.awayToSection _ _ (awayMonomial R t e)).1 ⟨x.1, _⟩).val = _
  rw [val_awayToSection_awayMonomial_apply, val_awayToSection_awayMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The open `⋂_{i ∈ s} D₊(xᵢ)` of `ℙ¹_k`. -/
abbrev chart (s : Set (ULift.{u} (Fin 2))) : (ProjectiveLine (Spec (.of k))).Opens :=
  toProjInt _ (Spec (.of k)) ⁻¹ᵁ basicOpenInt _ s

lemma chart_mono {s t : Set (ULift.{u} (Fin 2))} (hts : t ⊆ s) : chart k s ≤ chart k t :=
  (toProjInt _ _).preimage_mono (Proj.basicOpen_monomialToNat_indicator_mono hts)

/-- The functions on `⋂_{i ∈ s} D₊(xᵢ)` coming from the degree-zero localization of
`ℤ[x₀, x₁]` away from `∏_{i ∈ s} xᵢ`. -/
def chartFun (s : Set (ULift.{u} (Fin 2))) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (monomialToNat (ULift.{u} ℤ) (s.indicator 1)) →+* Γ(ProjectiveLine (Spec (.of k)), chart k s) :=
  (Proj.awayToSection _ _ ≫ (toProjInt _ (Spec (.of k))).appLE (basicOpenInt _ s)
    (chart k s) le_rfl).hom

/-- The constant functions on an open of `ℙ¹_k`. -/
def chartConst (V : (ProjectiveLine (Spec (.of k))).Opens) :
    k →+* Γ(ProjectiveLine (Spec (.of k)), V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appTop ≫
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE le_top).op).hom

lemma presheaf_map_chartConst {V W : (ProjectiveLine (Spec (.of k))).Opens} (h : W ≤ V) (c : k) :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE h).op (chartConst k V c) =
      chartConst k W c := by
  simp only [chartConst, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.presheaf_map_map_apply]
  rfl

lemma presheaf_map_chartFun_awayMonomial {s t : Set (ULift.{u} (Fin 2))} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (chart_mono k hts)).op
        (chartFun k t (awayMonomial _ t e)) =
      chartFun k s (awayMonomial _ s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) := by
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.appLE_map (toProjInt _ (Spec (.of k)))
    (U := basicOpenInt _ t) (le_rfl : chart k t ≤ _) (homOfLE (chart_mono k hts)).op)
    (Proj.awayToSection _ _ (awayMonomial _ t e))
  have h2 := ConcreteCategory.congr_hom (Scheme.Hom.map_appLE (toProjInt _ (Spec (.of k)))
    (U := basicOpenInt _ s) (V := chart k s) le_rfl
    (homOfLE (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts)).op)
    (Proj.awayToSection _ _ (awayMonomial _ t e))
  rw [CommRingCat.comp_apply] at h1 h2
  erw [Proj.presheaf_map_awayToSection_awayMonomial hts] at h2
  exact h1.trans h2.symm

section Coordinates

variable {i j : ULift.{u} (Fin 2)} (hij : i ≠ j)

include hij in
lemma eq_or_eq_of_ne (l : ULift.{u} (Fin 2)) : l = i ∨ l = j := by
  obtain ⟨⟨i, hi⟩⟩ := i
  obtain ⟨⟨j, hj⟩⟩ := j
  obtain ⟨⟨l, hl⟩⟩ := l
  simp only [ne_eq, ULift.up.injEq, Fin.mk.injEq] at hij ⊢
  omega

include hij in
lemma sum_eq_add_of_ne {M : Type*} [AddCommMonoid M] (f : ULift.{u} (Fin 2) → M) :
    ∑ l, f l = f i + f j :=
  Fintype.sum_eq_add i j hij fun l hl ↦ ((eq_or_eq_of_ne hij l).elim hl.1 hl.2).elim

/-- The exponent vector of the affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
def coordExp : laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 :=
  ⟨Pi.single j 1 - Pi.single i 1, by simp [Finset.sum_sub_distrib], fun l hl ↦ by
    rw [Set.mem_singleton_iff] at hl
    simp only [Pi.sub_apply, Pi.single_apply, if_neg hl, sub_zero]
    split_ifs <;> norm_num⟩

/-- The affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
def coord : Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  chartFun k {i} (awayMonomial _ {i} (coordExp (i := i) (j := j)))

/-- Every Laurent monomial regular on `D₊(xᵢ)` is a power of `xⱼ / xᵢ`. -/
def coordExpEquiv : ℕ ≃ laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 where
  toFun m := ⟨m • (coordExp (i := i) (j := j)).1, by
    simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, (coordExp (i := i) (j := j)).2.1,
      mul_zero],
    fun l hl ↦ nsmul_nonneg ((coordExp (i := i) (j := j)).2.2 l hl) m⟩
  invFun e := (e.1 j).toNat
  left_inv m := by simp [coordExp, hij.symm]
  right_inv e := by
    have hj := e.2.2 j (by simpa using hij.symm)
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    refine Subtype.ext (funext fun l ↦ ?_)
    rcases eq_or_eq_of_ne hij l with rfl | rfl
    · simp [coordExp, hij]
      omega
    · simp [coordExp, hij.symm]
      omega

lemma chartFun_coordExpEquiv (m : ℕ) :
    chartFun k {i} (awayMonomial _ _ (coordExpEquiv hij m)) = coord k (i := i) (j := j) ^ m := by
  rw [coord, ← map_pow, ← Proj.awayMonomial_pow _ m (coordExpEquiv hij m) rfl]

/-- The ring homomorphism `k[X] → Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
def polyToChart : Polynomial k →+* Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  Polynomial.eval₂RingHom (chartConst k (chart k {i})) (coord k (i := i) (j := j))

include hij in
/-- **The functions on the standard chart `D₊(xᵢ)` of `ℙ¹_k` are the polynomials in
`xⱼ / xᵢ`.** -/
lemma bijective_polyToChart : Function.Bijective (polyToChart k (i := i) (j := j)) := by
  have hB := bijective_sum_awayMonomial (n := ULift.{u} (Fin 2)) k (Set.singleton_nonempty i)
  let g : Polynomial k ≃ (laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 →₀ k) :=
    (Polynomial.toFinsuppIso k).toEquiv.trans
      ((AddMonoidAlgebra.coeffEquiv (R := k) (M := ℕ)).trans
        (Finsupp.equivCongrLeft (coordExpEquiv hij)))
  convert hB.comp g.bijective using 1
  funext p
  rw [Function.comp_apply]
  simp only [g, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    Polynomial.toFinsuppIso_apply, AddMonoidAlgebra.coeffEquiv_apply,
    Finsupp.equivCongrLeft_apply, Finsupp.sum_equivMapDomain]
  rw [polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finsupp.sum, Polynomial.support_toFinsupp]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Polynomial.toFinsupp_apply, ← chartFun_coordExpEquiv k hij]
  rfl

/-- The ring isomorphism `k[X] ≅ Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
def polyEquivChart : Polynomial k ≃+* Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  RingEquiv.ofBijective _ (bijective_polyToChart k hij)

lemma polyEquivChart_apply (p : Polynomial k) :
    polyEquivChart k hij p = polyToChart k (i := i) (j := j) p :=
  rfl

lemma polyEquivChart_symm_coord :
    (polyEquivChart k hij).symm (coord k (i := i) (j := j)) = Polynomial.X :=
  (polyEquivChart k hij).symm_apply_eq.2 (by simp [polyEquivChart_apply, polyToChart])

lemma polyEquivChart_symm_chartConst (c : k) :
    (polyEquivChart k hij).symm (chartConst k _ c) = Polynomial.C c :=
  (polyEquivChart k hij).symm_apply_eq.2 (by simp [polyEquivChart_apply, polyToChart])

end Coordinates

section Charts

lemma isAffineOpen_chart {s : Set (ULift.{u} (Fin 2))} (hs : s.Nonempty) :
    IsAffineOpen (chart k s) := by
  have : IsAffineHom (toProjInt (ULift.{u} (Fin 2)) (Spec (.of k))) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  exact (Proj.isAffineOpen_basicOpen _ _ (monomialToNat_indicator_mem (ULift.{u} ℤ) s)
    (indicatorDegree_pos hs)).preimage _

/-- The generator `xᵢ⁻²` of `𝒪(-2)` over `D₊(xᵢ)`. -/
def twistGen (i : ULift.{u} (Fin 2)) :
    Γ(twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2), chart k {i}) :=
  twistMonomialSection (Spec (.of k)) {i}
    (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))

lemma isFreeGenerator_twistGen (i : ULift.{u} (Fin 2)) : IsFreeGenerator (twistGen k i) :=
  isFreeGenerator_twistMonomialSection_singleExponent _

variable {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (σ : ℤ)

/-- The derivation `σ d / d(xⱼ / xᵢ)` of `Γ(D₊(xᵢ)) = k[xⱼ / xᵢ]`, with values in `𝒪(-2)`
through its generator `xᵢ⁻²`. -/
def chartDerivation :
    Γ(ProjectiveLine (Spec (.of k)), chart k {i}) →+
      Γ(twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2), chart k {i}) where
  toFun f := σ • ((polyEquivChart k hij
    (Polynomial.derivative ((polyEquivChart k hij).symm f))) • twistGen k i)
  map_zero' := by simp
  map_add' f g := by simp [add_smul]

lemma chartDerivation_apply (f : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    chartDerivation k hij σ f = σ • ((polyEquivChart k hij
      (Polynomial.derivative ((polyEquivChart k hij).symm f))) • twistGen k i) :=
  rfl

lemma chartDerivation_mul (f g : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    chartDerivation k hij σ (f * g) =
      f • chartDerivation k hij σ g + g • chartDerivation k hij σ f := by
  simp only [chartDerivation_apply, map_mul, Polynomial.derivative_mul, map_add,
    RingEquiv.apply_symm_apply, add_smul, mul_smul, smul_add]
  module

lemma chartDerivation_coord :
    chartDerivation k hij σ (coord k (i := i) (j := j)) = σ • twistGen k i := by
  simp [chartDerivation_apply, polyEquivChart_symm_coord]

lemma chartDerivation_chartConst (c : k) : chartDerivation k hij σ (chartConst k _ c) = 0 := by
  simp [chartDerivation_apply, polyEquivChart_symm_chartConst]

/-- The local derivation over `D₊(xᵢ)` extending `chartDerivation`. -/
def chartLocalDerivation : LocalDerivation (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2))
    (chart k {i}) :=
  LocalDerivation.ofIsAffineOpen (isAffineOpen_chart k (Set.singleton_nonempty i))
    (chartDerivation k hij σ) (chartDerivation_mul k hij σ)

end Charts

section Overlap

/-- The intersection `D₊(x₀) ∩ D₊(x₁)`. -/
abbrev overlap : (ProjectiveLine (Spec (.of k))).Opens := chart k Set.univ

lemma overlap_le_chart (i : ULift.{u} (Fin 2)) : overlap k ≤ chart k {i} :=
  chart_mono k (Set.subset_univ _)

lemma mem_chart_iff {s : Set (ULift.{u} (Fin 2))} {x : ProjectiveLine (Spec (.of k))} :
    x ∈ chart k s ↔ ∀ i ∈ s, x ∈ standardOpen _ (Spec (.of k)) i :=
  Proj.mem_basicOpen_monomialToNat_indicator

lemma chart_singleton (i : ULift.{u} (Fin 2)) : chart k {i} = standardOpen _ (Spec (.of k)) i :=
  Opens.ext (Set.ext fun _ ↦ (mem_chart_iff k).trans (by simp))

lemma le_overlap {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) {W : (ProjectiveLine (Spec (.of k))).Opens}
    (hi : W ≤ chart k {i}) (hj : W ≤ chart k {j}) : W ≤ overlap k := fun _ hx ↦
  (mem_chart_iff k).2 fun l _ ↦ (eq_or_eq_of_ne hij l).elim
    (fun h ↦ h ▸ chart_singleton k i ▸ hi hx) fun h ↦ h ▸ chart_singleton k j ▸ hj hx

lemma iSup_chart : ⨆ i, chart k {i} = ⊤ := by
  simp only [chart_singleton, iSup_standardOpen]

variable {i j : ULift.{u} (Fin 2)}

/-- The Laurent monomial `xⱼ / xᵢ` on the overlap. -/
def overlapCoordExp (i j : ULift.{u} (Fin 2)) : laurentExponents (Set.univ : Set (ULift.{u} (Fin 2))) 0 :=
  ⟨(coordExp (i := i) (j := j)).1, (coordExp (i := i) (j := j)).2.1, fun _ hl ↦ (hl trivial).elim⟩

lemma coord_restrict :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)) =
      chartFun k Set.univ (awayMonomial _ _ (overlapCoordExp i j)) :=
  presheaf_map_chartFun_awayMonomial k (Set.subset_univ _) _

lemma coord_mul_coord :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)) *
      (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i)) = 1 := by
  rw [coord_restrict, coord_restrict, ← map_mul,
    Proj.awayMonomial_mul _ _ ⟨0, by simp, fun _ _ ↦ le_rfl⟩ (by
      funext l
      simp only [overlapCoordExp, coordExp, Pi.zero_apply, Pi.add_apply, Pi.sub_apply]
      ring),
    Proj.awayMonomial_zero _ rfl, map_one]

lemma twistGen_restrict :
    (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k i)).op (twistGen k i) =
      ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j))) ^ 2 •
      (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k j)).op (twistGen k j) := by
  have hi := twist_presheaf_map_twistMonomialSection (S := Spec (.of k)) (m := -2)
    (Set.subset_univ {i}) (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))
  have hj := twist_presheaf_map_twistMonomialSection (S := Spec (.of k)) (m := -2)
    (Set.subset_univ {j}) (Proj.singleExponent (s := {j}) (m := -2) (Set.mem_singleton j))
  rw [twistGen, twistGen, hi, hj, twistMonomialSection_eq_smul (Set.mem_univ j), coord_restrict,
    ← map_pow, ← Proj.awayMonomial_pow _ 2 _ ?_]
  · rfl
  · funext l
    simp only [Proj.shiftExponent, Proj.singleExponent, overlapCoordExp, coordExp, Pi.sub_apply,
      Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all

lemma closure_overlap (hij : i ≠ j) :
    Subring.closure (Set.range (chartConst k (overlap k)) ∪
      {(ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)),
       (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i))}) = ⊤ := by
  set T := Subring.closure (Set.range (chartConst k (overlap k)) ∪
      {(ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)),
       (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i))})
  have hmono (e : laurentExponents (Set.univ : Set (ULift.{u} (Fin 2))) 0) :
      chartFun k Set.univ (awayMonomial _ _ e) ∈ T := by
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    rcases le_total 0 (e.1 j) with h | h
    · rw [Proj.awayMonomial_pow (overlapCoordExp i j) (e.1 j).toNat e ?_, map_pow,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
    · rw [Proj.awayMonomial_pow (overlapCoordExp j i) (e.1 i).toNat e ?_, map_pow,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
  refine eq_top_iff.2 fun f _ ↦ ?_
  obtain ⟨c, rfl⟩ := (bijective_sum_awayMonomial (n := ULift.{u} (Fin 2)) k
    (Set.univ_nonempty (α := ULift.{u} (Fin 2)))).2 f
  refine Subring.sum_mem _ fun e _ ↦ Subring.mul_mem _
    (Subring.subset_closure (Or.inl ⟨c e, rfl⟩)) (hmono e)

end Overlap

end AlgebraicGeometry.ProjectiveLine
