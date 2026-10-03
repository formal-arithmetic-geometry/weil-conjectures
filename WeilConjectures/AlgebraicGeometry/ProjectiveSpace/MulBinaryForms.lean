/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
public import WeilConjectures.Mathlib.RingTheory.Polynomial.ContentIdeal

/-!
# Multiplication of binary forms

A point of `ℙᵈ` with homogeneous coordinates `(x₀ : ⋯ : x_d)` is the same as a nonzero binary
form `∑ₐ xₐ tᵃ` of degree `d` up to scalars. Multiplying binary forms defines a morphism
`ℙᵈ × ℙᵉ ⟶ ℙᵈ⁺ᵉ`, sending a pair of points `(xₐ)`, `(y_b)` to the point with homogeneous
coordinates `c_k = ∑_{a + b = k} xₐ y_b`.

Like the Segre morphism, it is constructed chart by chart on the integral models: on the chart
`D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` the sections `c_k / (Xᵢ Yⱼ)` are the coefficients of the product of the
binary forms `A = ∑ₐ (Xₐ / Xᵢ) tᵃ` and `B = ∑_b (Y_b / Yⱼ) tᵇ`. As `A` and `B` both have a
coefficient equal to `1`, their content ideals are the unit ideal, hence so is the content
ideal of `A B` by the lemma of Gauss (`Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top`),
i.e. the sections `c_k / (Xᵢ Yⱼ)` generate the unit ideal. On an overlap of two charts the
binary forms `A`, `B` change by units, so the chart morphisms glue.

The relative version over a base scheme `S` is stated with source the iterated projective
space `ℙᵉ_{ℙᵈ_S}`, which is how `ℙᵈ_S ×_S ℙᵉ_S` arises in iterated constructions.

## Main definitions

- `AlgebraicGeometry.Proj.chartBinaryForm`: the binary form `∑ₐ (Xₐ / Xᵢ) tᵃ` on (a scheme
  over) the `i`-th standard chart of `ℙᵈ_ℤ`.
- `AlgebraicGeometry.Proj.mulBinaryForms`: the morphism `ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ ⟶ ℙᵈ⁺ᵉ_ℤ`.
- `AlgebraicGeometry.ProjectiveSpace.mulBinaryForms`: the morphism `ℙᵉ_{ℙᵈ_S} ⟶ ℙᵈ⁺ᵉ_S` over
  `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial (homogeneousSubmodule awayXRatio)

section ChartBinaryForm

variable {d : ℕ} {V : Scheme.{u}} (i : ULift.{u} (Fin (d + 1)))

/-- The binary form `∑ₐ (Xₐ / Xᵢ) tᵃ` of degree `d`, pulled back to a scheme `V` along a
morphism `q` to the `i`-th standard chart `Spec (ℤ[X]_{Xᵢ})₀` of `ℙᵈ_ℤ`. -/
def chartBinaryForm
    (q : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1))) (ULift.{u} ℤ))
      (MvPolynomial.X i))) : Polynomial Γ(V, ⊤) :=
  ∑ a : ULift.{u} (Fin (d + 1)), Polynomial.monomial a.down.val
    (((Scheme.ΓSpecIso _).inv ≫ q.appTop).hom (awayXRatio (ULift.{u} ℤ) i a))

variable (q : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1)))
  (ULift.{u} ℤ)) (MvPolynomial.X i)))

/-- The `a`-th coefficient of `chartBinaryForm i q` is the pullback of `Xₐ / Xᵢ`. -/
lemma coeff_chartBinaryForm (a : ULift.{u} (Fin (d + 1))) :
    (chartBinaryForm i q).coeff a.down.val =
      ((Scheme.ΓSpecIso _).inv ≫ q.appTop).hom (awayXRatio (ULift.{u} ℤ) i a) := by
  rw [chartBinaryForm, Polynomial.finsetSum_coeff, Finset.sum_eq_single a]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h ↦ hb (ULift.ext _ _ (Fin.ext h))
  · simp

/-- The `i`-th coefficient of `chartBinaryForm i q` is `1`. -/
lemma coeff_chartBinaryForm_self : (chartBinaryForm i q).coeff i.down.val = 1 := by
  rw [coeff_chartBinaryForm, MvPolynomial.awayXRatio_self, map_one]

lemma natDegree_chartBinaryForm_le : (chartBinaryForm i q).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ ↦
    (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp a.down.isLt)

/-- The content ideal of `chartBinaryForm i q` is the unit ideal, as its `i`-th coefficient
is `1`. -/
lemma contentIdeal_chartBinaryForm : (chartBinaryForm i q).contentIdeal = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← coeff_chartBinaryForm_self i q]
  exact Polynomial.coeff_mem_contentIdeal _ _

/-- `chartBinaryForm` is natural in the scheme `V`. -/
lemma map_chartBinaryForm {W : Scheme.{u}} (c : W ⟶ V) :
    (chartBinaryForm i q).map c.appTop.hom = chartBinaryForm i (c ≫ q) := by
  simp only [chartBinaryForm, Polynomial.map_sum, Polynomial.map_monomial]
  rfl

/-- On a scheme mapping compatibly to the `i`-th and `i'`-th standard charts of `ℙᵈ_ℤ`, the
binary forms `chartBinaryForm` of the two charts differ by the factor `Xᵢ / Xᵢ'`. -/
lemma chartBinaryForm_eq_C_mul (i' : ULift.{u} (Fin (d + 1)))
    (q' : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1)))
      (ULift.{u} ℤ)) (MvPolynomial.X i')))
    (h : q ≫ awayι _ (MvPolynomial.X i) (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)
        Nat.one_pos =
      q' ≫ awayι _ (MvPolynomial.X i') (MvPolynomial.X_mem_homogeneousSubmodule_one _ i')
        Nat.one_pos) :
    chartBinaryForm i' q' =
      Polynomial.C (((Scheme.ΓSpecIso _).inv ≫ q'.appTop).hom
        (awayXRatio (ULift.{u} ℤ) i' i)) * chartBinaryForm i q := by
  have hX : ∀ k : ULift.{u} (Fin (d + 1)), (MvPolynomial.X k : MvPolynomial _ (ULift.{u} ℤ)) ∈
      homogeneousSubmodule _ (ULift.{u} ℤ) (1 • 1) := fun k ↦ by
    simpa using MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) k
  simp only [chartBinaryForm, Finset.mul_sum, Polynomial.C_mul_monomial]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact congrArg (Polynomial.monomial _)
    ((appTop_awayMk_eq_mul _ Nat.one_pos _ _ q q' h (hX i) (MvPolynomial.X a) (hX a)).trans
      (mul_comm _ _))

/-- The factor `Xᵢ / Xᵢ'` relating the binary forms of two standard charts is a unit. -/
lemma isUnit_chartBinaryForm_factor (i' : ULift.{u} (Fin (d + 1)))
    (q' : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1)))
      (ULift.{u} ℤ)) (MvPolynomial.X i')))
    (h : q ≫ awayι _ (MvPolynomial.X i) (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)
        Nat.one_pos =
      q' ≫ awayι _ (MvPolynomial.X i') (MvPolynomial.X_mem_homogeneousSubmodule_one _ i')
        Nat.one_pos) :
    IsUnit (((Scheme.ΓSpecIso _).inv ≫ q'.appTop).hom (awayXRatio (ULift.{u} ℤ) i' i)) := by
  have hX : ∀ k : ULift.{u} (Fin (d + 1)), (MvPolynomial.X k : MvPolynomial _ (ULift.{u} ℤ)) ∈
      homogeneousSubmodule _ (ULift.{u} ℤ) (1 • 1) := fun k ↦ by
    simpa using MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) k
  exact isUnit_appTop_awayMk _ Nat.one_pos _ _ q q' h (hX i) (hX i')

end ChartBinaryForm

section MulChartBinaryForm

variable {d e : ℕ} {V : Scheme.{u}} (i : ULift.{u} (Fin (d + 1))) (j : ULift.{u} (Fin (e + 1)))
  (qa : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1)))
    (ULift.{u} ℤ)) (MvPolynomial.X i)))
  (qb : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (e + 1)))
    (ULift.{u} ℤ)) (MvPolynomial.X j)))

/-- The coefficients of a product of two `chartBinaryForm`s are natural in the scheme. -/
lemma appTop_coeff_mul_chartBinaryForm {W : Scheme.{u}} (c : W ⟶ V) (n : ℕ) :
    c.appTop.hom ((chartBinaryForm i qa * chartBinaryForm j qb).coeff n) =
      (chartBinaryForm i (c ≫ qa) * chartBinaryForm j (c ≫ qb)).coeff n := by
  rw [← Polynomial.coeff_map, Polynomial.map_mul, map_chartBinaryForm, map_chartBinaryForm]

/-- Changing the charts multiplies the coefficients of a product of two `chartBinaryForm`s by
the product of the transition factors. -/
lemma coeff_mul_chartBinaryForm_eq_mul (i' : ULift.{u} (Fin (d + 1)))
    (qa' : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (d + 1)))
      (ULift.{u} ℤ)) (MvPolynomial.X i')))
    (ha : qa ≫ awayι _ (MvPolynomial.X i) (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)
        Nat.one_pos =
      qa' ≫ awayι _ (MvPolynomial.X i') (MvPolynomial.X_mem_homogeneousSubmodule_one _ i')
        Nat.one_pos)
    (j' : ULift.{u} (Fin (e + 1)))
    (qb' : V ⟶ Spec (.of <| Away (homogeneousSubmodule (ULift.{u} (Fin (e + 1)))
      (ULift.{u} ℤ)) (MvPolynomial.X j')))
    (hb : qb ≫ awayι _ (MvPolynomial.X j) (MvPolynomial.X_mem_homogeneousSubmodule_one _ j)
        Nat.one_pos =
      qb' ≫ awayι _ (MvPolynomial.X j') (MvPolynomial.X_mem_homogeneousSubmodule_one _ j')
        Nat.one_pos) (n : ℕ) :
    (chartBinaryForm i' qa' * chartBinaryForm j' qb').coeff n =
      ((Scheme.ΓSpecIso _).inv ≫ qa'.appTop).hom (awayXRatio (ULift.{u} ℤ) i' i) *
        ((Scheme.ΓSpecIso _).inv ≫ qb'.appTop).hom (awayXRatio (ULift.{u} ℤ) j' j) *
        (chartBinaryForm i qa * chartBinaryForm j qb).coeff n := by
  rw [chartBinaryForm_eq_C_mul i qa i' qa' ha, chartBinaryForm_eq_C_mul j qb j' qb' hb,
    mul_mul_mul_comm, ← Polynomial.C_mul, Polynomial.coeff_C_mul]

end MulChartBinaryForm

variable (d e : ℕ)

set_option hygiene false in
/-- The open cover of `ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ` by products of standard charts. -/
local notation "𝒰" d:max e:max =>
  segreCover (ULift.{u} (Fin (d + 1))) (ULift.{u} (Fin (e + 1)))

/-- The section `c_k / (Xᵢ Yⱼ)` of the `(i, j)`-chart of `ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ`: the `k`-th
coefficient of the product of the binary forms `∑ₐ (Xₐ / Xᵢ) tᵃ` and `∑_b (Y_b / Yⱼ) tᵇ`. -/
def mulChartSection (i : ULift.{u} (Fin (d + 1))) (j : ULift.{u} (Fin (e + 1)))
    (k : ULift.{u} (Fin (d + e + 1))) : Γ((𝒰 d e).X (i, j), ⊤) :=
  (chartBinaryForm i (segreCoverFst i j) * chartBinaryForm j (segreCoverSnd i j)).coeff
    k.down.val

/-- The sections `mulChartSection` of a chart generate the unit ideal, by the lemma of Gauss
on the content ideal of a product of polynomials. -/
lemma span_range_mulChartSection_eq_top (i : ULift.{u} (Fin (d + 1)))
    (j : ULift.{u} (Fin (e + 1))) :
    Ideal.span (Set.range (mulChartSection d e i j)) = ⊤ := by
  have hP := Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top
    (contentIdeal_chartBinaryForm i (segreCoverFst i j))
    (contentIdeal_chartBinaryForm j (segreCoverSnd i j))
  rw [eq_top_iff, ← hP, ← Polynomial.span_range_coeff, Ideal.span_le]
  rintro _ ⟨N, rfl⟩
  by_cases hN : N < d + e + 1
  · exact Ideal.subset_span ⟨⟨⟨N, hN⟩⟩, rfl⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · exact zero_mem _
    · exact (Polynomial.natDegree_mul_le.trans (add_le_add
        (natDegree_chartBinaryForm_le _ _) (natDegree_chartBinaryForm_le _ _))).trans_lt
        (by omega)

/-- Multiplication of binary forms on the `(i, j)`-chart of `ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ`: the morphism to
`ℙᵈ⁺ᵉ_ℤ` sending the homogeneous coordinate `Z_k` to `mulChartSection d e i j k`. -/
def mulChartHom (i : ULift.{u} (Fin (d + 1))) (j : ULift.{u} (Fin (e + 1))) :
    (𝒰 d e).X (i, j) ⟶
      projectiveSpaceOverAffine (ULift.{u} (Fin (d + e + 1))) (ULift.{u} ℤ) :=
  fromOfGlobalSections _ (ProjectiveSpace.evalSections (mulChartSection d e i j))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_mulChartSection_eq_top d e i j))

/-- The chart morphisms `mulChartHom` agree on the overlap of two charts: the defining
sections differ by the unit `(Xᵢ / Xᵢ') (Yⱼ / Yⱼ')`. -/
lemma mulChartHom_compatible (i i' : ULift.{u} (Fin (d + 1))) (j j' : ULift.{u} (Fin (e + 1))) :
    pullback.fst ((𝒰 d e).f (i, j)) ((𝒰 d e).f (i', j')) ≫
        mulChartHom d e i j =
      pullback.snd ((𝒰 d e).f (i, j)) ((𝒰 d e).f (i', j')) ≫
        mulChartHom d e i' j' := by
  set p₁ := pullback.fst ((𝒰 d e).f (i, j)) ((𝒰 d e).f (i', j'))
  set p₂ := pullback.snd ((𝒰 d e).f (i, j)) ((𝒰 d e).f (i', j'))
  have hcond : p₁ ≫ (𝒰 d e).f (i, j) = p₂ ≫ (𝒰 d e).f (i', j') :=
    pullback.condition
  have ha : (p₁ ≫ segreCoverFst i j) ≫ awayι _ (MvPolynomial.X i)
        (MvPolynomial.X_mem_homogeneousSubmodule_one _ i) Nat.one_pos =
      (p₂ ≫ segreCoverFst i' j') ≫ awayι _ (MvPolynomial.X i')
        (MvPolynomial.X_mem_homogeneousSubmodule_one _ i') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverFst_awayι, segreCoverFst_awayι]
    exact (reassoc_of% hcond) _
  have hb : (p₁ ≫ segreCoverSnd i j) ≫ awayι _ (MvPolynomial.X j)
        (MvPolynomial.X_mem_homogeneousSubmodule_one _ j) Nat.one_pos =
      (p₂ ≫ segreCoverSnd i' j') ≫ awayι _ (MvPolynomial.X j')
        (MvPolynomial.X_mem_homogeneousSubmodule_one _ j') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverSnd_awayι, segreCoverSnd_awayι]
    exact (reassoc_of% hcond) _
  have hA := isUnit_chartBinaryForm_factor i _ i' _ ha
  have hB := isUnit_chartBinaryForm_factor j _ j' _ hb
  have hvar (k : ULift.{u} (Fin (d + e + 1))) : p₂.appTop.hom (mulChartSection d e i' j' k) =
      ((hA.unit * hB.unit : Γ(_, ⊤)ˣ) : Γ(_, ⊤)) *
        p₁.appTop.hom (mulChartSection d e i j k) := by
    refine (appTop_coeff_mul_chartBinaryForm i' j' _ _ p₂ _).trans
      ((coeff_mul_chartBinaryForm_eq_mul i j _ _ i' _ ha j' _ hb _).trans ?_)
    rw [Units.val_mul]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hA.unit_spec.symm hB.unit_spec.symm)
      (appTop_coeff_mul_chartBinaryForm i j _ _ p₁ _).symm
  refine (comp_fromOfGlobalSections _ p₁ _ _ (map_irrelevant_comp_appTop_eq_top _ p₁ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_mulChartSection_eq_top d e i j)))).trans
    (Eq.trans ?_ (comp_fromOfGlobalSections _ p₂ _ _ (map_irrelevant_comp_appTop_eq_top _ p₂ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_mulChartSection_eq_top d e i' j')))).symm)
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ (hA.unit * hB.unit) _ _ (fun n a hna ↦ ?_) _ _
  exact (RingHom.congr_fun (ProjectiveSpace.comp_evalSections p₂ _) a).trans
    ((congrArg (fun s ↦ ProjectiveSpace.evalSections s a) (funext hvar)).trans
      ((ProjectiveSpace.evalSections_const_mul _ _ hna).trans
        (congrArg _ (RingHom.congr_fun (ProjectiveSpace.comp_evalSections p₁ _) a).symm)))

/-- **Multiplication of binary forms** `ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ ⟶ ℙᵈ⁺ᵉ_ℤ` on the integral models,
sending a pair of points with homogeneous coordinates `(xₐ)`, `(y_b)` to the point with
homogeneous coordinates `c_k = ∑_{a + b = k} xₐ y_b`, the coefficients of the product of the
binary forms `∑ₐ xₐ tᵃ` and `∑_b y_b tᵇ`. It is glued from the chart morphisms
`mulChartHom`. -/
def mulBinaryForms :
    pullback (terminal.from (projectiveSpaceOverAffine (ULift.{u} (Fin (d + 1))) (ULift.{u} ℤ)))
        (terminal.from (projectiveSpaceOverAffine (ULift.{u} (Fin (e + 1))) (ULift.{u} ℤ))) ⟶
      projectiveSpaceOverAffine (ULift.{u} (Fin (d + e + 1))) (ULift.{u} ℤ) :=
  (𝒰 d e).glueMorphisms (fun ij ↦ mulChartHom d e ij.1 ij.2)
    fun ij ij' ↦ mulChartHom_compatible d e ij.1 ij'.1 ij.2 ij'.2

/-- On the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`, multiplication of binary forms is `mulChartHom d e i j`. -/
@[reassoc]
lemma segreCover_f_comp_mulBinaryForms (i : ULift.{u} (Fin (d + 1)))
    (j : ULift.{u} (Fin (e + 1))) :
    (𝒰 d e).f (i, j) ≫ mulBinaryForms d e = mulChartHom d e i j :=
  (𝒰 d e).ι_glueMorphisms _ _ (i, j)

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

variable (d e : ℕ) (S : Scheme.{u})

/-- The morphism `ℙᵉ_{ℙᵈ_S} ⟶ ℙᵈ_ℤ ×_ℤ ℙᵉ_ℤ` to the product of the integral models. -/
def iterToProjInt :
    ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ⟶
      pullback
        (terminal.from (Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (d + 1))) (ULift.{u} ℤ)))
        (terminal.from (Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (e + 1))) (ULift.{u} ℤ))) :=
  pullback.lift (ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ↘ _ ≫
    toProjInt _ S) (toProjInt _ _) (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma iterToProjInt_fst :
    iterToProjInt d e S ≫ pullback.fst _ _ =
      ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ↘ _ ≫ toProjInt _ S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma iterToProjInt_snd :
    iterToProjInt d e S ≫ pullback.snd _ _ = toProjInt _ _ :=
  pullback.lift_snd _ _ _

/-- **Multiplication of binary forms** `ℙᵉ_{ℙᵈ_S} ⟶ ℙᵈ⁺ᵉ_S` over a base scheme `S`, the base
change of `AlgebraicGeometry.Proj.mulBinaryForms` along the structure morphism of `S`. It
sends a pair of points with homogeneous coordinates `(xₐ)`, `(y_b)` to the point with
homogeneous coordinates `c_k = ∑_{a + b = k} xₐ y_b`. -/
def mulBinaryForms :
    ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ⟶
      ℙ(ULift.{u} (Fin (d + e + 1)); S) :=
  pullback.lift (ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ↘ _ ≫
    ℙ(ULift.{u} (Fin (d + 1)); S) ↘ S) (iterToProjInt d e S ≫ Proj.mulBinaryForms d e)
    (terminal.hom_ext _ _)

/-- Multiplication of binary forms is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma mulBinaryForms_over :
    mulBinaryForms d e S ≫ ℙ(ULift.{u} (Fin (d + e + 1)); S) ↘ S =
      ℙ(ULift.{u} (Fin (e + 1)); ℙ(ULift.{u} (Fin (d + 1)); S)) ↘ _ ≫
        ℙ(ULift.{u} (Fin (d + 1)); S) ↘ S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mulBinaryForms_toProjInt :
    mulBinaryForms d e S ≫ toProjInt _ S = iterToProjInt d e S ≫ Proj.mulBinaryForms d e :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.ProjectiveSpace
