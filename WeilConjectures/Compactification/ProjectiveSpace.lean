/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import WeilConjectures.Mathlib.Algebra.DirectSum.Internal
public import WeilConjectures.RingTheory.Dehomogenization

/-!

# Relative projective space

For an index type `n` and a scheme `S` we define the relative projective space
`ℙ(n; S)`, mirroring Mathlib's construction of the relative affine space `𝔸(n; S)`: it is
the base change to `S` of the integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`, where the
polynomial ring carries its total-degree grading.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpaceInt` — the integral model `ℙⁿ_ℤ`.
- `AlgebraicGeometry.RelativeProjectiveSpace` — the relative projective space `ℙ(n; S)`,
  with its structure morphism `ℙ(n; S) ↘ S`.
- `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace` — the standard affine chart
  `𝔸(n; S) ⟶ ℙ(n; S)`, given on the integral model by `Tᵢ ↦ Tᵢ / T₀`.

## Main results

- `AlgebraicGeometry.RelativeProjectiveSpace.isProper_over` — for finite `n`, the structure
  morphism `ℙ(n; S) ⟶ S` is proper.
- `AlgebraicGeometry.AffineSpace.isOpenImmersion_toRelativeProjectiveSpace` — the standard
  chart is an open immersion, and it is a morphism over `S` by
  `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace_over`.

## Implementation notes

Mathlib does not make the total-degree grading of `MvPolynomial σ R` a global instance; it is
enabled here as a local instance. As in `WeilConjectures.Blowup.Affine.Projective`, the
integral model is a plain definition rather than an abbreviation, so that the grading
instance does not leak into the statements below.

The name `RelativeProjectiveSpace` is used because `AlgebraicGeometry.ProjectiveSpace` is
already taken by the projective space `Proj A[T]` over an affine base of
`WeilConjectures.Blowup.Affine.Projective`.

## Blueprint

This file implements `def:nagata-relative-projective-space`,
`lemma:nagata-projective-is-proper` and `lemma:nagata-relative-affine-space-open-immersion`
of the Nagata compactification blueprint. Note that this Mathlib has no morphism class
`IsProjective` for schemes, so `lemma:nagata-projective-is-proper` is formalized in the only
form in which it is used, namely properness of `ℙ(n; S) ⟶ S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))

local notation3 "𝒪[" n "]" => MvPolynomial.homogeneousSubmodule (Option n) (ULift ℤ)

/-- The integral model `ℙⁿ_ℤ` of projective `n`-space: `Proj` of the polynomial ring
`ℤ[T₀, …, Tₙ]` in the variables `Option n` with its total-degree grading. -/
noncomputable def ProjectiveSpaceInt : Scheme.{u} := Proj 𝒪[n]

/-- `ℙ(n; S)` is the projective `n`-space over `S`, the base change of the integral model
`ℙⁿ_ℤ` along `S ⟶ Spec ℤ`.
(blueprint: `def:nagata-relative-projective-space`) -/
noncomputable def RelativeProjectiveSpace : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (ProjectiveSpaceInt n))

/-- `ℙ(n; S)` is the projective `n`-space over `S`. This notation is local to the files
that use `RelativeProjectiveSpace`, since `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
exports the same notation for its own base-change model `AlgebraicGeometry.ProjectiveSpace`. -/
local notation "ℙ(" n "; " S ")" => RelativeProjectiveSpace n S

namespace RelativeProjectiveSpace

@[simps -isSimp]
noncomputable instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `ℙⁿ_ℤ`. -/
noncomputable def toProjectiveSpaceInt : ℙ(n; S) ⟶ ProjectiveSpaceInt n := pullback.snd _ _

lemma isPullback_over :
    IsPullback (toProjectiveSpaceInt n S) (ℙ(n; S) ↘ S)
      (terminal.from (ProjectiveSpaceInt n)) (terminal.from S) :=
  (IsPullback.of_hasPullback _ _).flip

section Proper

variable [Finite n]

instance finiteType_gradeZero :
    Algebra.FiniteType (𝒪[n] 0) (MvPolynomial (Option n) (ULift ℤ)) :=
  .of_restrictScalars_finiteType (ULift ℤ) _ _

/-- The degree-zero part of `ℤ[T₀, …, Tₙ]` is `ℤ`, so its spectrum is a terminal scheme. -/
noncomputable def specGradeZeroIsTerminal : IsTerminal (Spec (.of (𝒪[n] 0))) :=
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.homogeneousSubmoduleZeroEquiv (σ := Option n) (R := ULift ℤ)).toRingHom) :=
    ⟨CommRingCat.ofHom (MvPolynomial.homogeneousSubmoduleZeroEquiv (σ := Option n)
      (R := ULift ℤ)).symm.toRingHom, by ext a; simp, by ext a; simp⟩
  specULiftZIsTerminal.ofIso (asIso (Spec.map (CommRingCat.ofHom
    (MvPolynomial.homogeneousSubmoduleZeroEquiv (σ := Option n) (R := ULift ℤ)).toRingHom))).symm

/-- The integral model `ℙⁿ_ℤ` is proper over `Spec ℤ`, for finite `n`. -/
theorem isProper_terminalFrom_projectiveSpaceInt :
    IsProper (terminal.from (ProjectiveSpaceInt n)) := by
  have h : IsProper (Proj.toSpecZero 𝒪[n] ≫
      ((specGradeZeroIsTerminal n).uniqueUpToIso terminalIsTerminal).hom) := by
    rw [MorphismProperty.cancel_right_of_respectsIso @IsProper]
    infer_instance
  rwa [Subsingleton.elim (Proj.toSpecZero 𝒪[n] ≫
    ((specGradeZeroIsTerminal n).uniqueUpToIso terminalIsTerminal).hom)
    (terminal.from (ProjectiveSpaceInt n))] at h

/-- **The relative projective space is proper over its base**: for finite `n`, the structure
morphism `ℙ(n; S) ⟶ S` is proper.
(blueprint: `lemma:nagata-projective-is-proper`) -/
instance isProper_over : IsProper (ℙ(n; S) ↘ S) :=
  have := isProper_terminalFrom_projectiveSpaceInt n
  inferInstanceAs (IsProper (pullback.fst _ _))

end Proper

end RelativeProjectiveSpace

namespace AffineSpace

/-- The standard affine chart of the integral model: the open immersion
`𝔸ⁿ_ℤ ⟶ ℙⁿ_ℤ` onto `D₊(T₀)`, given by `Tᵢ ↦ Tᵢ / T₀`. -/
noncomputable def toProjectiveSpaceInt : Spec ℤ[n] ⟶ ProjectiveSpaceInt n :=
  Spec.map (dehomogenizeEquiv n (ULift ℤ)).toCommRingCatIso.hom ≫
    Proj.awayι 𝒪[n] (X none) isHomogeneous_X_none Nat.one_pos

instance isOpenImmersion_toProjectiveSpaceInt : IsOpenImmersion (toProjectiveSpaceInt n) := by
  rw [toProjectiveSpaceInt]
  infer_instance

/-- **The standard affine chart of the relative projective space**: the open immersion
`𝔸(n; S) ⟶ ℙ(n; S)` over `S` identifying `𝔸(n; S)` with the standard open `D₊(T₀)`.
(blueprint: `lemma:nagata-relative-affine-space-open-immersion`) -/
noncomputable def toRelativeProjectiveSpace : 𝔸(n; S) ⟶ ℙ(n; S) :=
  pullback.lift (𝔸(n; S) ↘ S) (toSpecMvPoly n S ≫ toProjectiveSpaceInt n)
    (Subsingleton.elim _ _)

@[reassoc (attr := simp)]
lemma toRelativeProjectiveSpace_over :
    toRelativeProjectiveSpace n S ≫ ℙ(n; S) ↘ S = 𝔸(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toRelativeProjectiveSpace_toProjectiveSpaceInt :
    toRelativeProjectiveSpace n S ≫ RelativeProjectiveSpace.toProjectiveSpaceInt n S =
      toSpecMvPoly n S ≫ toProjectiveSpaceInt n :=
  pullback.lift_snd _ _ _

/-- The standard chart of `ℙ(n; S)` is the base change of the standard chart of the
integral model `ℙⁿ_ℤ`. -/
lemma isPullback_toRelativeProjectiveSpace :
    IsPullback (toSpecMvPoly n S) (toRelativeProjectiveSpace n S) (toProjectiveSpaceInt n)
      (RelativeProjectiveSpace.toProjectiveSpaceInt n S) := by
  refine IsPullback.of_bot ?_ (toRelativeProjectiveSpace_toProjectiveSpaceInt n S).symm
    (RelativeProjectiveSpace.isPullback_over n S)
  rw [toRelativeProjectiveSpace_over, Subsingleton.elim (toProjectiveSpaceInt n ≫
    terminal.from (ProjectiveSpaceInt n)) (terminal.from (Spec ℤ[n]))]
  exact (IsPullback.of_hasPullback _ _).flip

instance isOpenImmersion_toRelativeProjectiveSpace :
    IsOpenImmersion (toRelativeProjectiveSpace n S) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_toRelativeProjectiveSpace n S) inferInstance

end AffineSpace

end AlgebraicGeometry
