/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

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

## Implementation notes

Mathlib does not make the total-degree grading of `MvPolynomial σ A` a global instance, since
one may want to grade by another weight function; it is enabled here as a local instance. To
keep it out of the statements of the results below, `Proj.mvPolynomial σ A` is a plain
definition rather than an abbreviation, so that downstream files need not re-enable the
instance.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

section Affine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type u) (A : Type u) [CommRing A]

/-- The base ring is isomorphic to the degree-zero piece of `A[T]` for the total-degree
grading, via `a ↦ C a`. -/
def mvPolynomialGradingZero :
    A ≃+* MvPolynomial.homogeneousSubmodule σ A 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C σ a⟩
  invFun p := MvPolynomial.coeff 0 (p : MvPolynomial σ A)
  left_inv a := by simp
  right_inv p := Subtype.ext <| by
    have h : (p : MvPolynomial σ A).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.2
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm
  map_mul' a b := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp]
lemma coe_mvPolynomialGradingZero (a : A) :
    (mvPolynomialGradingZero σ A a : MvPolynomial σ A) = MvPolynomial.C a :=
  rfl

/-- The projective space `ℙ^σ_A` over an affine base, defined as `Proj` of the polynomial
ring `A[T]` in the variables `σ` with its total-degree grading.
(blueprint: `def:nagata-affine-blowup-projective-embedding`) -/
def Proj.mvPolynomial : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule σ A)

/-- The structure morphism `ℙ^σ_A ⟶ Spec A` of the projective space over an affine base. -/
def Proj.mvPolynomialToSpec : Proj.mvPolynomial σ A ⟶ Spec (.of A) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ A) ≫
    Spec.map (CommRingCat.ofHom (mvPolynomialGradingZero σ A).toRingHom)

end Affine

/-- `ℙ(n; S)` is the projective `n`-space over `S`, that is, the base change
`S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model along the structure morphism of `S`.
Note that `n : Type u` indexes the *homogeneous* coordinates, so that the classical `ℙⁿ_S` is
`ℙ(Fin (n + 1); S)`. -/
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

/-- `ℙ(n; S)` is functorial in the base `S`. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.lift ((ℙ(n; S) ↘ S) ≫ f) (toProjMvPoly n S) (terminal.hom_ext _ _)

variable {S}

@[reassoc (attr := simp)]
lemma map_over {T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ ℙ(n; T) ↘ T = (ℙ(n; S) ↘ S) ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_toProjMvPoly {T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toProjMvPoly n T = toProjMvPoly n S :=
  pullback.lift_snd _ _ _

variable (S)

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := by
  refine pullback.hom_ext ?_ ?_
  · change map n (𝟙 S) ≫ ℙ(n; S) ↘ S = 𝟙 _ ≫ ℙ(n; S) ↘ S
    simp
  · change map n (𝟙 S) ≫ toProjMvPoly n S = 𝟙 _ ≫ toProjMvPoly n S
    simp

variable {S}

@[reassoc, simp]
lemma map_comp {S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  refine pullback.hom_ext ?_ ?_
  · change map n (f ≫ g) ≫ ℙ(n; S'') ↘ S'' = (map n f ≫ map n g) ≫ ℙ(n; S'') ↘ S''
    simp
  · change map n (f ≫ g) ≫ toProjMvPoly n S'' = (map n f ≫ map n g) ≫ toProjMvPoly n S''
    simp

end ProjectiveSpace

end AlgebraicGeometry
