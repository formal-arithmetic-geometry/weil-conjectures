/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The Segre morphism between the integral models of projective spaces

The Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ` sends a pair of points with homogeneous
coordinates `(xₖ)ₖ` and `(yₗ)ₗ` to the point with homogeneous coordinates `(xₖ · yₗ)_{k,l}`.
Here `ℙ^σ_ℤ` is the integral model `Proj.projectiveSpaceOverAffine σ (ULift ℤ)` of projective
space, and the product is the fibre product over the terminal scheme, matching the way
`AlgebraicGeometry.ProjectiveSpace` is defined.

There is no formula for the Segre morphism in terms of global sections of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, as
the product has no nonconstant global functions. It is therefore constructed chart by chart:
on the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` the sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` generate the unit ideal,
since the `(i, j)`-th one is `1`, so `AlgebraicGeometry.Proj.fromOfGlobalSections` applies and
gives a morphism to `ℙ^(n×m)_ℤ`. Two such chart morphisms agree on an overlap because their
defining sections differ by the unit `(Xᵢ / Xᵢ') · (Yⱼ / Yⱼ')`, and
`AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_unit_pow_mul` says that rescaling by a unit
does not change the induced morphism. The chart morphisms therefore glue.

Whether the Segre morphism is a closed immersion, and the relative version over an arbitrary
base scheme, are not treated here.

## Main definitions

- `AlgebraicGeometry.Proj.segre` — the Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ`.
- `AlgebraicGeometry.Proj.segreCover` — the standard open cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the
  products `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of standard charts.
- `AlgebraicGeometry.Proj.segreChartHom` — the Segre morphism on the `(i, j)`-chart.

## Main results

- `AlgebraicGeometry.Proj.segreCover_f_comp_segre` — on the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`, the
  Segre morphism is `segreChartHom i j`.

## Blueprint

This is the absolute case of `def:chow-segre`; the relative Segre morphism over a base scheme
and the multiple product are built from it elsewhere.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

section Cover

variable (σ A : Type u) [CommRing A]

/-- The standard affine open cover of `ℙ^σ_A` by the charts `D₊(Xᵢ) ≅ Spec (A[X]_{Xᵢ})₀`. -/
def projectiveSpaceOverAffineAffineOpenCover :
    (projectiveSpaceOverAffine σ A).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun i : σ ↦ MvPolynomial.X i)
    (fun i ↦ X_mem_homogeneousSubmodule_one A i) (fun _ ↦ Nat.one_pos)
    (toIdeal_irrelevant_homogeneousSubmodule σ A).le

@[simp]
lemma projectiveSpaceOverAffineAffineOpenCover_X (i : σ) :
    (projectiveSpaceOverAffineAffineOpenCover σ A).X i =
      CommRingCat.of (Away (homogeneousSubmodule σ A) (MvPolynomial.X i)) := rfl

@[simp]
lemma projectiveSpaceOverAffineAffineOpenCover_f (i : σ) :
    (projectiveSpaceOverAffineAffineOpenCover σ A).f i =
      awayι _ (MvPolynomial.X i) (X_mem_homogeneousSubmodule_one A i) Nat.one_pos := rfl

end Cover

variable (n m : Type u)

/-- The open cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the products `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of standard charts
of the two factors. -/
def segreCover :
    (pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
      (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projectiveSpaceOverAffineAffineOpenCover n (ULift.{u} ℤ)).openCover
    (projectiveSpaceOverAffineAffineOpenCover m (ULift.{u} ℤ)).openCover _ _

variable {n m}

/-- The projection of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `i`-th standard chart of
the first factor. -/
def segreCoverFst (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶
      Spec (.of <| Away (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i)) :=
  pullback.fst _ _

/-- The projection of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `j`-th standard chart of
the second factor. -/
def segreCoverSnd (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶
      Spec (.of <| Away (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X j)) :=
  pullback.snd _ _

@[reassoc]
lemma segreCoverFst_awayι (i : n) (j : m) :
    segreCoverFst i j ≫ awayι _ (MvPolynomial.X i)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos =
      (segreCover n m).f (i, j) ≫ pullback.fst _ _ := by
  simp [segreCover, segreCoverFst]

@[reassoc]
lemma segreCoverSnd_awayι (i : n) (j : m) :
    segreCoverSnd i j ≫ awayι _ (MvPolynomial.X j)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j) Nat.one_pos =
      (segreCover n m).f (i, j) ≫ pullback.snd _ _ := by
  simp [segreCover, segreCoverSnd]

/-- The section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. It is the
image of the homogeneous coordinate `W_{k,l}` of `ℙ^(n×m)_ℤ` under the Segre morphism. -/
def segreChartSection (i : n) (j : m) (kl : n × m) : Γ((segreCover n m).X (i, j), ⊤) :=
  ((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst i j).appTop).hom
      (awayXRatio (ULift.{u} ℤ) i kl.1) *
    ((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd i j).appTop).hom
      (awayXRatio (ULift.{u} ℤ) j kl.2)

@[simp]
lemma segreChartSection_self (i : n) (j : m) : segreChartSection i j (i, j) = 1 := by
  simp [segreChartSection]

lemma span_range_segreChartSection_eq_top (i : n) (j : m) :
    Ideal.span (Set.range (segreChartSection i j)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← segreChartSection_self i j]
  exact Ideal.subset_span ⟨(i, j), rfl⟩

/-- The Segre morphism on the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the morphism to
`ℙ^(n×m)_ℤ` sending the homogeneous coordinate `W_{k,l}` to `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
def segreChartHom (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶ projectiveSpaceOverAffine (n × m) (ULift.{u} ℤ) :=
  fromOfGlobalSections _ (ProjectiveSpace.evalSections (segreChartSection i j))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top i j))

section Compatibility

variable (i i' : n) (j j' : m)

/-- The chart morphisms `segreChartHom` agree on the overlap of two charts of the standard
cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the two chart morphisms differ by rescaling the homogeneous
coordinates of `ℙ^(n×m)_ℤ` by the unit `(Xᵢ / Xᵢ') · (Yⱼ / Yⱼ')`. -/
lemma segreChartHom_compatible :
    pullback.fst ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫ segreChartHom i j =
      pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫
        segreChartHom i' j' := by
  have hXi : ∀ k : n, (MvPolynomial.X k : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXj : ∀ l : m, (MvPolynomial.X l : MvPolynomial m (ULift.{u} ℤ)) ∈
      homogeneousSubmodule m (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXi1 : ∀ k : n, (MvPolynomial.X k : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) (1 • 1) := fun k ↦ by simpa using hXi k
  have hXj1 : ∀ l : m, (MvPolynomial.X l : MvPolynomial m (ULift.{u} ℤ)) ∈
      homogeneousSubmodule m (ULift.{u} ℤ) (1 • 1) := fun l ↦ by simpa using hXj l
  set p₁ := pullback.fst ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j'))
  set p₂ := pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j'))
  have hcond : p₁ ≫ (segreCover n m).f (i, j) = p₂ ≫ (segreCover n m).f (i', j') :=
    pullback.condition
  have ha : (p₁ ≫ segreCoverFst i j) ≫ awayι _ (MvPolynomial.X i) (hXi i) Nat.one_pos =
      (p₂ ≫ segreCoverFst i' j') ≫ awayι _ (MvPolynomial.X i') (hXi i') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverFst_awayι, segreCoverFst_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hb : (p₁ ≫ segreCoverSnd i j) ≫ awayι _ (MvPolynomial.X j) (hXj j) Nat.one_pos =
      (p₂ ≫ segreCoverSnd i' j') ≫ awayι _ (MvPolynomial.X j') (hXj j') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverSnd_awayι, segreCoverSnd_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hA : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
      (awayXRatio (ULift.{u} ℤ) i' i)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXi i) (hXi i') _ _ ha (hXi1 i) (hXi1 i')
  have hB : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
      (awayXRatio (ULift.{u} ℤ) j' j)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXj j) (hXj j') _ _ hb (hXj1 j) (hXj1 j')
  have hpull : ∀ {R : CommRingCat.{u}} {W V : Scheme.{u}} (c : V ⟶ W) (q : W ⟶ Spec R) (z : R),
      c.appTop.hom (((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom z) =
        ((Scheme.ΓSpecIso R).inv ≫ (c ≫ q).appTop).hom z := fun _ _ _ ↦ rfl
  have hvar : ∀ kl : n × m, p₂.appTop.hom (segreChartSection i' j' kl) =
      ((hA.unit * hB.unit : Γ(_, ⊤)ˣ) : Γ(_, ⊤)) *
        p₁.appTop.hom (segreChartSection i j kl) := by
    intro kl
    have h1 : ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
        (awayXRatio (ULift.{u} ℤ) i' kl.1) =
        ((Scheme.ΓSpecIso _).inv ≫ (p₁ ≫ segreCoverFst i j).appTop).hom
            (awayXRatio (ULift.{u} ℤ) i kl.1) *
          ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
            (awayXRatio (ULift.{u} ℤ) i' i) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXi i) (hXi i') _ _ ha (hXi1 i)
        (MvPolynomial.X kl.1) (hXi1 kl.1)
    have h2 : ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
        (awayXRatio (ULift.{u} ℤ) j' kl.2) =
        ((Scheme.ΓSpecIso _).inv ≫ (p₁ ≫ segreCoverSnd i j).appTop).hom
            (awayXRatio (ULift.{u} ℤ) j kl.2) *
          ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
            (awayXRatio (ULift.{u} ℤ) j' j) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXj j) (hXj j') _ _ hb (hXj1 j)
        (MvPolynomial.X kl.2) (hXj1 kl.2)
    simp only [segreChartSection, map_mul, hpull, h1, h2, Units.val_mul, IsUnit.unit_spec]
    ring
  simp only [segreChartHom]
  rw [comp_fromOfGlobalSections _ p₁ _ _ (map_irrelevant_comp_appTop_eq_top _ p₁ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top i j))),
    comp_fromOfGlobalSections _ p₂ _ _ (map_irrelevant_comp_appTop_eq_top _ p₂ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top i' j')))]
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ (hA.unit * hB.unit) _ _ (fun d a hda ↦ ?_) _ _
  rw [ProjectiveSpace.comp_evalSections, ProjectiveSpace.comp_evalSections]
  simp only [hvar]
  exact ProjectiveSpace.evalSections_const_mul _ _ hda

end Compatibility

variable (n m)

/-- **The Segre morphism** `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ` between the integral models of
projective spaces, sending a pair of points with homogeneous coordinates `(xₖ)` and `(yₗ)` to
the point with homogeneous coordinates `(xₖ · yₗ)`.

It is glued from the morphisms `segreChartHom i j` on the standard cover of the product by the
charts `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`. -/
def segre :
    pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
        (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⟶
      projectiveSpaceOverAffine (n × m) (ULift.{u} ℤ) :=
  (segreCover n m).glueMorphisms (fun ij ↦ segreChartHom ij.1 ij.2)
    fun ij ij' ↦ segreChartHom_compatible ij.1 ij'.1 ij.2 ij'.2

variable {n m}

/-- On the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the Segre morphism is the morphism
`segreChartHom i j` given by the sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
@[reassoc]
lemma segreCover_f_comp_segre (i : n) (j : m) :
    (segreCover n m).f (i, j) ≫ segre n m = segreChartHom i j :=
  (segreCover n m).ι_glueMorphisms _ _ (i, j)

end AlgebraicGeometry.Proj
