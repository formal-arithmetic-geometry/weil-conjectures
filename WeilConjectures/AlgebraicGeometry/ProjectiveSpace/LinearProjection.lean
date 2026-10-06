/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Linear projections of `Proj` to projective space

Let `A` be a commutative `k`-algebra graded by `𝒜 : ℕ → Submodule k A`, and let `l : ι → A` be
a family of elements of degree one such that the basic opens `D₊(lᵢ)` cover `Proj 𝒜`. Then
`l` defines a morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)`, `x ↦ [lᵢ(x)]`. On the chart `D₊(lᵢ)` it is the
morphism given by the global sections `lⱼ / lᵢ` of `Spec (A_{lᵢ})₀`, which generate the unit
ideal since `lᵢ / lᵢ = 1`. Two such chart morphisms agree on the overlap `D₊(lᵢ lⱼ)`, as their
sections differ by the unit `lᵢ / lⱼ`, so they glue.

The case of a pair `l₀, l₁` gives the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`, which on `D₊(l₀)`
corresponds to the ring map `k[t] → A_(l₀)`, `t ↦ l₁ / l₀`, and on `D₊(l₁)` to the ring map
`k[t⁻¹] → A_(l₁)`, `t⁻¹ ↦ l₀ / l₁`.

## Main definitions

- `AlgebraicGeometry.Proj.toSpecBase` — the structure morphism `Proj 𝒜 ⟶ Spec k`.
- `AlgebraicGeometry.Proj.linearChartHom` — the morphism `Spec (A_{lᵢ})₀ ⟶ ℙ(ι; Spec k)`
  given by the sections `lⱼ / lᵢ`.
- `AlgebraicGeometry.Proj.linearProjection` — the morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)` defined by
  a family of linear forms without common zero.
- `AlgebraicGeometry.Proj.linearPairProjection` — the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.comp_homOfSections` — naturality of `homOfSections`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_eq_of_unit_mul` — rescaling the sections
  by a unit does not change `homOfSections`.
- `AlgebraicGeometry.Proj.linearChartHom_compatible` — the chart morphisms agree on overlaps.
- `AlgebraicGeometry.Proj.awayι_linearProjection` — on the chart `D₊(lᵢ)` the linear
  projection is `linearChartHom`.
- `AlgebraicGeometry.Proj.linearProjection_over` — the linear projection is a morphism over
  `Spec k`.
- `AlgebraicGeometry.Proj.isFinite_linearPairProjection` — `π_{l₀,l₁}` is finite for a
  standard graded `k`-algebra.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y S : Scheme.{u}} {n : Type u}

/-- If global sections `s i` generate the unit ideal, so do their pullbacks along any
morphism of schemes. -/
lemma span_range_appTop_eq_top (h : Y ⟶ X) {s : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range fun i ↦ h.appTop.hom (s i)) = ⊤ := by
  rw [Set.range_comp' h.appTop.hom s, ← Ideal.map_span, hs, Ideal.map_top]

/-- `homOfSections` is natural in the source: precomposing with `h : Y ⟶ X` gives the morphism
attached to `h ≫ g` and the pulled back sections. -/
@[reassoc]
lemma comp_homOfSections (h : Y ⟶ X) (g : X ⟶ S) (s : n → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    h ≫ homOfSections g s hs =
      homOfSections (h ≫ g) (fun i ↦ h.appTop.hom (s i)) (span_range_appTop_eq_top h hs) := by
  refine hom_ext n S (by simp) ?_
  rw [Category.assoc, homOfSections_toProjInt, homOfSections_toProjInt,
    Proj.comp_fromOfGlobalSections _ h _ _ (Proj.map_irrelevant_comp_appTop_eq_top _ h _
      (map_irrelevant_evalSections_eq_top s hs))]
  congr 1
  exact comp_evalSections h s

/-- Rescaling all the sections by a unit `u` of `Γ(X, ⊤)` does not change `homOfSections`. -/
lemma homOfSections_eq_of_unit_mul (g : X ⟶ S) (u : Γ(X, ⊤)ˣ) {s s' : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) (hs' : Ideal.span (Set.range s') = ⊤)
    (hss' : ∀ i, s' i = u * s i) :
    homOfSections g s hs = homOfSections g s' hs' := by
  obtain rfl : s' = fun i ↦ u * s i := funext hss'
  refine hom_ext n S (by simp) ?_
  rw [homOfSections_toProjInt, homOfSections_toProjInt]
  exact Proj.fromOfGlobalSections_eq_of_unit_pow_mul _ u _ _
    (fun _ _ ha ↦ evalSections_const_mul _ _ ha) _ _

end ProjectiveSpace

namespace Proj

section Construction

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- The structure morphism `Proj 𝒜 ⟶ Spec k` of the projective spectrum of a graded
`k`-algebra, i.e. `Proj 𝒜 ⟶ Spec A₀ ⟶ Spec k`. -/
def toSpecBase : Proj 𝒜 ⟶ Spec (.of k) :=
  toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))

variable {ι : Type u} (l : ι → A) (hl : ∀ i, l i ∈ 𝒜 1)

/-- The global section `lⱼ / lᵢ` of the chart `Spec (A_{lᵢ})₀` of `Proj 𝒜`. -/
def linearChartSection (i j : ι) : Γ(Spec (.of (Away 𝒜 (l i))), ⊤) :=
  (Scheme.ΓSpecIso _).inv.hom (Away.mk 𝒜 (hl i) 1 (l j) (by simpa using hl j))

@[simp]
lemma linearChartSection_self (i : ι) : linearChartSection 𝒜 l hl i i = 1 := by
  simp [linearChartSection, Away.mk_self]

lemma span_range_linearChartSection (i : ι) :
    Ideal.span (Set.range (linearChartSection 𝒜 l hl i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← linearChartSection_self 𝒜 l hl i]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The linear projection on the chart `D₊(lᵢ) = Spec (A_{lᵢ})₀` of `Proj 𝒜`: the morphism
to `ℙ(ι; Spec k)` sending the homogeneous coordinate `Tⱼ` to `lⱼ / lᵢ`
(blueprint: `def-pc-linear-pair-morphism`). -/
def linearChartHom (i : ι) : Spec (.of (Away 𝒜 (l i))) ⟶ ℙ(ι; Spec (.of k)) :=
  ProjectiveSpace.homOfSections (awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ toSpecBase 𝒜)
    (linearChartSection 𝒜 l hl i) (span_range_linearChartSection 𝒜 l hl i)

@[reassoc (attr := simp)]
lemma linearChartHom_over (i : ι) :
    linearChartHom 𝒜 l hl i ≫ ℙ(ι; Spec (.of k)) ↘ Spec (.of k) =
      awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ toSpecBase 𝒜 :=
  ProjectiveSpace.homOfSections_over _ _ _

/-- **The chart morphisms of a linear projection agree on overlaps**: on
`D₊(lᵢ) ∩ D₊(lⱼ) = D₊(lᵢ lⱼ)` the sections `lₘ / lᵢ` and `lₘ / lⱼ` differ by the unit
`lᵢ / lⱼ`, so the two chart morphisms coincide
(blueprint: `lem-pc-linear-pair-morphism-gluing`). -/
lemma linearChartHom_compatible (i j : ι) :
    pullback.fst (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos) ≫
        linearChartHom 𝒜 l hl i =
      pullback.snd (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos) ≫
        linearChartHom 𝒜 l hl j := by
  have h1 (m : ι) : l m ∈ 𝒜 (1 • 1) := by simpa using hl m
  set p₁ := pullback.fst (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos)
  set p₂ := pullback.snd (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos)
  have hcond : p₁ ≫ awayι 𝒜 (l i) (hl i) Nat.one_pos = p₂ ≫ awayι 𝒜 (l j) (hl j) Nat.one_pos :=
    pullback.condition
  have hu := isUnit_appTop_awayMk 𝒜 Nat.one_pos (hl i) (hl j) p₁ p₂ hcond (h1 i) (h1 j)
  rw [linearChartHom, linearChartHom, ProjectiveSpace.comp_homOfSections,
    ProjectiveSpace.comp_homOfSections, reassoc_of% hcond]
  refine ProjectiveSpace.homOfSections_eq_of_unit_mul _ hu.unit _ _ fun m ↦ ?_
  rw [IsUnit.unit_spec, mul_comm]
  exact appTop_awayMk_eq_mul 𝒜 Nat.one_pos (hl i) (hl j) p₁ p₂ hcond (h1 i) (l m) (h1 m)

variable (hcov : ⨆ i, basicOpen 𝒜 (l i) = ⊤)

/-- The open cover of `Proj 𝒜` by the charts `Spec (A_{lᵢ})₀ ≅ D₊(lᵢ)`, for a family of
elements `lᵢ` of degree one whose basic opens cover `Proj 𝒜`. -/
def linearCover : (Proj 𝒜).OpenCover :=
  .mkOfCovers ι (fun i ↦ Spec (.of (Away 𝒜 (l i)))) (fun i ↦ awayι 𝒜 (l i) (hl i) Nat.one_pos)
    fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
      rw [← opensRange_awayι 𝒜 _ (hl i) Nat.one_pos] at hi
      exact ⟨i, hi⟩

/-- **The linear projection** `Proj 𝒜 ⟶ ℙ(ι; Spec k)`, `x ↦ [lᵢ(x)]`, defined by a family of
elements `lᵢ` of degree one without common zero on `Proj 𝒜`. It is glued from the chart
morphisms `linearChartHom` (blueprint: `def-pc-linear-pair-morphism`). -/
def linearProjection : Proj 𝒜 ⟶ ℙ(ι; Spec (.of k)) :=
  (linearCover 𝒜 l hl hcov).glueMorphisms (linearChartHom 𝒜 l hl)
    (linearChartHom_compatible 𝒜 l hl)

/-- On the chart `D₊(lᵢ) = Spec (A_{lᵢ})₀`, the linear projection is the morphism given by the
sections `lⱼ / lᵢ`. -/
@[reassoc (attr := simp)]
lemma awayι_linearProjection (i : ι) :
    awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ linearProjection 𝒜 l hl hcov = linearChartHom 𝒜 l hl i :=
  (linearCover 𝒜 l hl hcov).ι_glueMorphisms _ _ i

/-- The linear projection is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
lemma linearProjection_over :
    linearProjection 𝒜 l hl hcov ≫ ℙ(ι; Spec (.of k)) ↘ Spec (.of k) = toSpecBase 𝒜 :=
  (linearCover 𝒜 l hl hcov).hom_ext _ _ fun i ↦ by
    rw [← Category.assoc]
    exact (awayι_linearProjection_assoc 𝒜 l hl hcov i _).trans (linearChartHom_over 𝒜 l hl i)

end Construction

section Pair

/-- The pair `(l₀, l₁)` as a family indexed by the index type `ULift (Fin 2)` of the
homogeneous coordinates of `ℙ¹`. -/
def linearPair {A : Type u} (l₀ l₁ : A) (i : ULift.{u} (Fin 2)) : A :=
  ![l₀, l₁] i.down

@[simp]
lemma linearPair_zero {A : Type u} (l₀ l₁ : A) : linearPair l₀ l₁ ⟨0⟩ = l₀ := rfl

@[simp]
lemma linearPair_one {A : Type u} (l₀ l₁ : A) : linearPair l₀ l₁ ⟨1⟩ = l₁ := rfl

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜] {l₀ l₁ : A}

omit [GradedAlgebra 𝒜] in
variable {𝒜} in
lemma linearPair_mem (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1) (i : ULift.{u} (Fin 2)) :
    linearPair l₀ l₁ i ∈ 𝒜 1 := by
  obtain ⟨i⟩ := i
  fin_cases i
  exacts [h₀, h₁]

lemma iSup_basicOpen_linearPair
    (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤) :
    ⨆ i, basicOpen 𝒜 (linearPair l₀ l₁ i) = ⊤ :=
  top_le_iff.mp <| hcov.symm.le.trans <|
    sup_le (le_iSup_of_le (⟨0⟩ : ULift.{u} (Fin 2)) le_rfl)
      (le_iSup_of_le (⟨1⟩ : ULift.{u} (Fin 2)) le_rfl)

variable {𝒜} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
  (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤)

/-- **The linear projection** `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`, `x ↦ [l₀(x) : l₁(x)]`, attached to
two elements `l₀, l₁` of degree one without common zero on `Proj 𝒜`. On `D₊(l₀)` it is given
by `t ↦ l₁ / l₀` and on `D₊(l₁)` by `t⁻¹ ↦ l₀ / l₁`
(blueprint: `def-pc-linear-pair-morphism`, `lem-pc-linear-pair-morphism-gluing`). -/
def linearPairProjection : Proj 𝒜 ⟶ ProjectiveLine (Spec (.of k)) :=
  linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁)
    (iSup_basicOpen_linearPair 𝒜 hcov)

/-- On the chart `D₊(l₀)`, `π_{l₀,l₁}` is the morphism given by the sections `(1, l₁ / l₀)`. -/
@[reassoc (attr := simp)]
lemma awayι_linearPairProjection_zero :
    awayι 𝒜 l₀ h₀ Nat.one_pos ≫ linearPairProjection h₀ h₁ hcov =
      linearChartHom 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) ⟨0⟩ :=
  awayι_linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) _ ⟨0⟩

/-- On the chart `D₊(l₁)`, `π_{l₀,l₁}` is the morphism given by the sections `(l₀ / l₁, 1)`. -/
@[reassoc (attr := simp)]
lemma awayι_linearPairProjection_one :
    awayι 𝒜 l₁ h₁ Nat.one_pos ≫ linearPairProjection h₀ h₁ hcov =
      linearChartHom 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) ⟨1⟩ :=
  awayι_linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) _ ⟨1⟩

/-- `π_{l₀,l₁}` is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
lemma linearPairProjection_over :
    linearPairProjection h₀ h₁ hcov ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) =
      toSpecBase 𝒜 :=
  linearProjection_over 𝒜 _ _ _

end Pair

/-- **`π_{l₀,l₁}` is finite** for a standard graded `k`-algebra, i.e. one with `A₀ = k` that is
generated by the finite-dimensional space `A₁` (blueprint:
`lem-pc-linear-pair-morphism-finite`). -/
theorem isFinite_linearPairProjection {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {𝒜 : ℕ → Submodule k A} [GradedAlgebra 𝒜] {l₀ l₁ : A} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
    (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤)
    (h0 : ∀ x ∈ 𝒜 0, ∃ c : k, algebraMap k A c = x)
    (hgen : Algebra.adjoin k (𝒜 1 : Set A) = ⊤) (hfin : Module.Finite k (𝒜 1)) :
    IsFinite (linearPairProjection h₀ h₁ hcov) :=
  sorry

end Proj

end AlgebraicGeometry
