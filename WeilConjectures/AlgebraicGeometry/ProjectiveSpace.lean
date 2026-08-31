/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Projective space over a base scheme

`ℙ(n; S)` is the projective `n`-space over an arbitrary base scheme `S`, defined as the base
change `S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model `ℙⁿ_ℤ = Proj ℤ[T]` along the structure
morphism of `S`, exactly as Mathlib's affine space `𝔸(n; S)` is defined as `S ×_{Spec ℤ} 𝔸ⁿ_ℤ`.
Here `n : Type u` is the index type of the *homogeneous* coordinates, so that the space Stacks
writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`.

Mathlib has no relative projective space to reuse, only the absolute `Proj` of a graded ring,
so everything below is new; the integral model itself is `Proj.mvPolynomial n (ULift.{u} ℤ)`.

## Main definitions

- `AlgebraicGeometry.Proj.mvPolynomial` — the projective space `ℙ^σ_A` over an affine base,
  i.e. `Proj` of the polynomial ring `A[T]` with its total-degree grading.
- `AlgebraicGeometry.Proj.mvPolynomialToSpec` — its structure morphism `ℙ^σ_A ⟶ Spec A`.
- `AlgebraicGeometry.ProjectiveSpace` — `ℙ(n; S)` is the projective `n`-space over `S`, with
  structure morphism `ℙ(n; S) ↘ S`.
- `AlgebraicGeometry.ProjectiveSpace.map` — functoriality of `ℙ(n; S)` in the base `S`.
- `AlgebraicGeometry.Proj.mvPolynomialChart` — the standard affine chart
  `𝔸^{σ ∖ {i}}_A ⟶ ℙ^σ_A` at a coordinate `i`, i.e. the standard open `D₊(X i)`.
- `AlgebraicGeometry.ProjectiveSpace.chart` — the standard affine chart
  `𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S)` of `ℙ(n; S)`, obtained from the chart of the integral model
  by base change.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.instIsProper` — for a finite index type, the structure
  morphism `ℙ(n; S) ↘ S` is proper.
- `AlgebraicGeometry.Proj.mvPolynomialAffineOpenCover` — the standard charts form an affine
  open cover of `ℙ^σ_A`, and `AlgebraicGeometry.ProjectiveSpace.chartCover` — the standard
  charts form an open cover of `ℙ(n; S)`. Together with
  `AlgebraicGeometry.ProjectiveSpace.isPullback_chart`, which exhibits each chart of
  `ℙ(n; S)` as the base change of a chart of `ℙⁿ_ℤ`, this is the chart interface of relative
  `Proj`: a morphism `X ⟶ ℙ(n; S)` can be built by gluing morphisms into the affine
  spaces `𝔸({j // j ≠ i}; S)`, which is what `AlgebraicGeometry.AffineSpace.homOfVector`
  provides.

## Implementation notes

Relative `Proj` over an *affine* base is Mathlib's `Proj.toSpecZero : Proj 𝒜 ⟶ Spec (𝒜 0)`,
for `𝒜` a graded ring; `Proj.mvPolynomialToSpec σ A : ℙ^σ_A ⟶ Spec A` is its projective-space
case, for `𝒜` the polynomial ring with its total-degree grading, and the charts below are the
`Spec (𝒜_f)₀` of that interface for `f` a variable.

Mathlib does not make the total-degree grading of `MvPolynomial σ A` a global instance, since
one may want to grade by another weight function; it is enabled here as a local instance. To
keep it out of the statements of the results below, `Proj.mvPolynomial σ A` is a plain
definition rather than an abbreviation, so that downstream files need not re-enable the
instance.

Defining `ℙ(n; S)` by base change is the cheap route: it needs no gluing, and properness of
`ℙ(n; S) ↘ S` follows from properness of the integral model by base change. The blueprint's
`def:nagata-relative-projective-space` instead constructs `ℙ^r_X` as the relative `Proj` of
a symmetric algebra, and requires its standard opens to be the relative spectra of the
degree-zero homogeneous localizations. Those standard opens are supplied here directly:
`ProjectiveSpace.chart` is the base change of the standard open `D₊(X i)` of the integral
model, and `ProjectiveSpace.chartCover` says that the charts cover, so `ℙ(n; S)` *is* glued
from the affine spaces `𝔸({j // j ≠ i}; S)` in the sense that matters for constructing
morphisms into it.

## TODO

- Relative `Proj` of a graded quasi-coherent algebra over an arbitrary base scheme, and the
  comparison `ℙ(n; S) ≅ Proj_S(Sym O_S^n)`. Mathlib has neither quasi-coherent sheaves of
  algebras nor relative `Spec`, and the gluing needs `Proj` to commute with base change, so
  this is a development of its own; the charts provided here are the part of its interface
  that the Nagata blueprint uses.
- `ℙ(n; Spec A) ≅ Proj.mvPolynomial n A` over `Spec A`, the analogue of
  `AlgebraicGeometry.AffineSpace.SpecIso`. This too needs `Proj` to commute with base change,
  so `Proj.mvPolynomial` and `ProjectiveSpace` are related here only through their charts.

## Blueprint

`ProjectiveSpace` implements `def:nagata-projective-space-base-change` of the Nagata
compactification blueprint, which is the base-change substitute for
`def:nagata-relative-projective-space` described above, and `ProjectiveSpace.instIsProper`
implements `lemma:nagata-projective-space-base-change-proper`. `Proj.mvPolynomial` is
`def:nagata-affine-proj` for a polynomial ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

section Affine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type u) (A : Type u) [CommRing A]

/-- The projective space `ℙ^σ_A` over an affine base, defined as `Proj` of the polynomial
ring `A[T]` in the variables `σ` with its total-degree grading.
(blueprint: `def:nagata-affine-proj`, for a polynomial ring) -/
def Proj.mvPolynomial : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule σ A)

/-- The structure morphism `ℙ^σ_A ⟶ Spec A` of the projective space over an affine base. -/
def Proj.mvPolynomialToSpec : Proj.mvPolynomial σ A ⟶ Spec (.of A) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ A) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.homogeneousSubmoduleZeroEquiv σ A).toRingHom)

/-- **Projective space over an affine base is proper**: for a finite index type `σ`, the
structure morphism `ℙ^σ_A ⟶ Spec A` is proper. -/
instance Proj.instIsProperMvPolynomialToSpec [Finite σ] :
    IsProper (Proj.mvPolynomialToSpec σ A) := by
  rw [Proj.mvPolynomialToSpec]
  infer_instance

section Charts

variable {σ A}

/-- The standard affine chart of `ℙ^σ_A` at the coordinate `i`, an open immersion
`𝔸^{σ ∖ {i}}_A = Spec A[X_j : j ≠ i] ⟶ ℙ^σ_A` with image the standard open `D₊(X i)`. -/
def Proj.mvPolynomialChart (i : σ) :
    Spec (.of (MvPolynomial {j // j ≠ i} A)) ⟶ Proj.mvPolynomial σ A :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.awayXEquiv i).toRingHom) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule σ A) (MvPolynomial.X i)
      (MvPolynomial.X_mem_homogeneousSubmodule i) Nat.one_pos

instance (i : σ) : IsOpenImmersion (Proj.mvPolynomialChart (A := A) i) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (MvPolynomial.awayXEquiv (R := A) i).toRingHom) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule σ A) (MvPolynomial.X i)
        (MvPolynomial.X_mem_homogeneousSubmodule i) Nat.one_pos))

open MvPolynomial in
/-- The standard chart `𝔸^{σ ∖ {i}}_A ⟶ ℙ^σ_A` has image the standard open `D₊(X i)`. -/
lemma Proj.opensRange_mvPolynomialChart (i : σ) :
    (Proj.mvPolynomialChart (A := A) i).opensRange =
      Proj.basicOpen (homogeneousSubmodule σ A) (X i) := by
  rw [← Proj.opensRange_awayι (homogeneousSubmodule σ A) (X i)
    (X_mem_homogeneousSubmodule (R := A) i) Nat.one_pos]
  exact Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (CommRingCat.ofHom (awayXEquiv (R := A) i).toRingHom))
    (Proj.awayι (homogeneousSubmodule σ A) (X i)
      (X_mem_homogeneousSubmodule (R := A) i) Nat.one_pos)

open MvPolynomial in
/-- The standard chart `𝔸^{σ ∖ {i}}_A ⟶ ℙ^σ_A` is a morphism over `Spec A`, given on rings
by the inclusion of the constants `A ⟶ A[X_j : j ≠ i]`. -/
@[reassoc]
lemma Proj.mvPolynomialChart_mvPolynomialToSpec (i : σ) :
    Proj.mvPolynomialChart (A := A) i ≫ Proj.mvPolynomialToSpec σ A =
      Spec.map (CommRingCat.ofHom (C : A →+* MvPolynomial {j // j ≠ i} A)) := by
  have key : (Spec.map (CommRingCat.ofHom (awayXEquiv (R := A) i).toRingHom) ≫
      Proj.awayι (homogeneousSubmodule σ A) (X i)
        (X_mem_homogeneousSubmodule (R := A) i) Nat.one_pos) ≫
      Proj.toSpecZero (homogeneousSubmodule σ A) ≫
        Spec.map (CommRingCat.ofHom (homogeneousSubmoduleZeroEquiv σ A).toRingHom) =
      Spec.map (CommRingCat.ofHom (C : A →+* MvPolynomial {j // j ≠ i} A)) := by
    rw [Category.assoc, Proj.awayι_toSpecZero_assoc (homogeneousSubmodule σ A) (X i)
        (X_mem_homogeneousSubmodule (R := A) i) Nat.one_pos,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r : 2
    simpa using awayXDehomogenize_fromZeroRingHom i (homogeneousSubmoduleZeroEquiv σ A r)
  -- `key` is the statement with `Proj.mvPolynomial` unfolded, which is what `rw` needs
  exact key

open MvPolynomial TopologicalSpace in
/-- **The standard charts cover projective space over an affine base**: the charts
`𝔸^{σ ∖ {i}}_A ⟶ ℙ^σ_A` form an affine open cover of `ℙ^σ_A`. -/
def Proj.mvPolynomialAffineOpenCover (σ A : Type u) [CommRing A] :
    (Proj.mvPolynomial σ A).AffineOpenCover where
  I₀ := σ
  X i := .of (MvPolynomial {j // j ≠ i} A)
  f i := Proj.mvPolynomialChart i
  idx x := (Opens.mem_iSup.mp ((Proj.iSup_basicOpen_eq_top (homogeneousSubmodule σ A) X
    (MvPolynomial.irrelevant_le_span_X σ A)).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.mvPolynomialChart (A := A) _).opensRange
    rw [Proj.opensRange_mvPolynomialChart]
    exact (Opens.mem_iSup.mp ((Proj.iSup_basicOpen_eq_top (homogeneousSubmodule σ A) X
      (MvPolynomial.irrelevant_le_span_X σ A)).ge (Set.mem_univ x))).choose_spec

end Charts

end Affine

/-- `ℙ(n; S)` is the projective `n`-space over `S`, that is, the base change
`S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model along the structure morphism of `S`.
Note that `n : Type u` indexes the *homogeneous* coordinates, so that the classical `ℙⁿ_S` is
`ℙ(Fin (n + 1); S)`.
(blueprint: `def:nagata-projective-space-base-change`) -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj.mvPolynomial n (ULift.{u} ℤ)))

namespace ProjectiveSpace

/-- `ℙ(n; S)` is the projective `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "ℙ(" n "; " S ")" => ProjectiveSpace n S

variable (n : Type u) (S : Scheme.{u})

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `ℙⁿ_ℤ`. -/
def toProjMvPoly : ℙ(n; S) ⟶ Proj.mvPolynomial n (ULift.{u} ℤ) := pullback.snd _ _

/-- A morphism into `ℙ(n; S)` is determined by its composites with the structure morphism to
`S` and with the map to the integral model `ℙⁿ_ℤ`. -/
@[ext 1100]
lemma hom_ext {X : Scheme.{u}} {f g : X ⟶ ℙ(n; S)}
    (h₁ : f ≫ ℙ(n; S) ↘ S = g ≫ ℙ(n; S) ↘ S)
    (h₂ : f ≫ toProjMvPoly n S = g ≫ toProjMvPoly n S) : f = g :=
  pullback.hom_ext h₁ h₂

/-- **`ℙ(n; S)` is proper over `S`**: for a finite index type `n`, the structure morphism
`ℙ(n; S) ↘ S` is proper, being a base change of the proper morphism `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
instance instIsProper [Finite n] : IsProper (ℙ(n; S) ↘ S) := by
  have hZ : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have hP : terminal.from (Proj.mvPolynomial n (ULift.{u} ℤ)) =
      Proj.mvPolynomialToSpec n (ULift.{u} ℤ) ≫ terminal.from _ := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := hZ ▸ inferInstance
  have : IsProper (terminal.from (Proj.mvPolynomial n (ULift.{u} ℤ))) := hP ▸ inferInstance
  exact inferInstanceAs (IsProper (pullback.fst _ _))

/-- `ℙ(n; S)` is functorial in the base `S`: `map n f` is the unique morphism making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commute and compatible with the maps to the integral model, i.e. making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
  toProjMvPoly    toProjMvPoly
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commute as well. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.lift (ℙ(n; S) ↘ S ≫ f) (toProjMvPoly n S) (terminal.hom_ext _ _)

/-- `map n f` is a morphism over `f`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ ℙ(n; T) ↘ T = ℙ(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

/-- `map n f` is compatible with the maps to the integral model `ℙⁿ_ℤ`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
  toProjMvPoly    toProjMvPoly
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_toProjMvPoly {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toProjMvPoly n T = toProjMvPoly n S :=
  pullback.lift_snd _ _ _

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := by
  ext1 <;> simp

@[reassoc, simp]
lemma map_comp {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1 <;> simp

section Charts

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine chart of `ℙ(n; S)` at the coordinate `i`, an open immersion
`𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S)` over `S`, obtained by base change from the standard chart
`D₊(X i)` of the integral model `ℙⁿ_ℤ`. -/
def chart (i : n) : 𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S) :=
  pullback.lift (𝔸({j // j ≠ i}; S) ↘ S)
    (AffineSpace.toSpecMvPoly _ S ≫ Proj.mvPolynomialChart i) (terminal.hom_ext _ _)

/-- The chart `𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S)` is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma chart_over (i : n) : chart n S i ≫ ℙ(n; S) ↘ S = 𝔸({j // j ≠ i}; S) ↘ S :=
  pullback.lift_fst _ _ _

/-- The chart `𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S)` is compatible with the maps to the integral
model. -/
@[reassoc (attr := simp)]
lemma chart_toProjMvPoly (i : n) :
    chart n S i ≫ toProjMvPoly n S =
      AffineSpace.toSpecMvPoly _ S ≫ Proj.mvPolynomialChart i :=
  pullback.lift_snd _ _ _

/-- **The charts of `ℙ(n; S)` are base changes of the charts of `ℙⁿ_ℤ`**: the square

```
                      chart n S i
  𝔸({j // j ≠ i}; S) ------------> ℙ(n; S)
          |                            |
          | toSpecMvPoly               | toProjMvPoly
          ↓                            ↓
  Spec ℤ[j : j ≠ i] ------------> ℙⁿ_ℤ
                  mvPolynomialChart i
```

is a pullback square. -/
lemma isPullback_chart (i : n) :
    IsPullback (chart n S i) (AffineSpace.toSpecMvPoly _ S) (toProjMvPoly n S)
      (Proj.mvPolynomialChart i) := by
  refine IsPullback.of_right (h₁₂ := ℙ(n; S) ↘ S) (X₂₃ := ⊤_ Scheme)
    (h₂₂ := terminal.from (Proj.mvPolynomial n (ULift.{u} ℤ))) (v₁₃ := terminal.from S)
    ?_ (chart_toProjMvPoly n S i) ?_
  · rw [chart_over, terminal.hom_ext (Proj.mvPolynomialChart (A := ULift.{u} ℤ) i ≫
      terminal.from (Proj.mvPolynomial n (ULift.{u} ℤ))) (terminal.from _)]
    exact IsPullback.of_hasPullback _ _
  · exact IsPullback.of_hasPullback _ _

instance (i : n) : IsOpenImmersion (chart n S i) := by
  apply MorphismProperty.of_isPullback (isPullback_chart n S i).flip
  infer_instance

/-- **The standard charts cover `ℙ(n; S)`**: the charts `𝔸({j // j ≠ i}; S) ⟶ ℙ(n; S)` form
an open cover of `ℙ(n; S)`. -/
def chartCover : ℙ(n; S).OpenCover :=
  Scheme.Cover.mkOfCovers n (fun i ↦ 𝔸({j // j ≠ i}; S)) (chart n S) fun x ↦ by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
        MvPolynomial.X (MvPolynomial.irrelevant_le_span_X n (ULift.{u} ℤ))).ge
        (Set.mem_univ ((toProjMvPoly n S).base x)))
    rw [← Proj.opensRange_mvPolynomialChart (A := ULift.{u} ℤ) i] at hi
    obtain ⟨z, hz⟩ := hi
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := toProjMvPoly n S) (g := Proj.mvPolynomialChart (A := ULift.{u} ℤ) i) x z hz.symm
    refine ⟨i, (isPullback_chart n S i).isoPullback.inv.base w, ?_⟩
    rw [← Scheme.Hom.comp_apply, (isPullback_chart n S i).isoPullback_inv_fst]
    exact hw₁

end Charts

end ProjectiveSpace

end AlgebraicGeometry
