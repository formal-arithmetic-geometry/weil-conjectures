/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Properness of morphisms of schemes over a base

Cancellation for properness, packaged for the category `Over S` of schemes over a base scheme
`S`: a morphism of `S`-schemes with proper source and separated target is proper. Properness —
and, separately, universal closedness — of the structure morphism of a scheme-theoretic fibre,
which is the corresponding property base changed along `Spec κ(y) ⟶ Y`. Together with the global
sections of a proper integral scheme over an algebraically closed field, which Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` gives outright.

Finally, a proper *affine* morphism is finite, because a morphism is integral exactly when it is
universally closed and affine, and finite exactly when it is integral and locally of finite type.
Over a field this says that a proper affine scheme `X` has finite-dimensional global sections, is
finite over the field, and — its global sections being an Artinian ring — has Krull dimension at
most zero.

## Main results

- `AlgebraicGeometry.isProper_left`: a morphism `f : X ⟶ Y` in `Over S` with `X` proper over `S`
  and `Y` separated over `S` is proper.
- `AlgebraicGeometry.isProper_fiberToSpecResidueField` and
  `AlgebraicGeometry.universallyClosed_fiberToSpecResidueField`: the structure morphism
  `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a proper, respectively universally closed,
  morphism is proper, respectively universally closed.
- `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop` (blueprint `lem:cube-global-sections`): for
  `X` proper and integral over an algebraically closed field `K`, the structure map
  `K ⟶ Γ(X, 𝒪_X)` is an isomorphism.
- `AlgebraicGeometry.isFinite_of_isAffineHom`: a proper affine morphism is finite.
- `AlgebraicGeometry.finite_ΓSpecIso_inv_comp_appTop`,
  `AlgebraicGeometry.isFinite_of_isAffine` and
  `AlgebraicGeometry.topologicalKrullDim_le_zero_of_isAffine` (blueprint
  `lem:deg-proper-affine-finite`): a proper affine scheme over a field `K` has
  finite-dimensional global sections, is finite over `K`, and has dimension at most zero.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` of schemes over `S` with `X` proper over `S` and `Y` separated over
`S` is proper.

```
             f.left
    X.left ─────────→ Y.left
         ╲           ╱
   X.hom  ╲         ╱  Y.hom
           ↘       ↙
               S
```
-/
instance (priority := low) isProper_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact IsProper.of_comp _ Y.hom

/-- The structure morphism `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a proper morphism
`f : X ⟶ Y` over `y : Y` is proper, being the base change of `f` along `Spec κ(y) ⟶ Y`.

```
    X_y ─────→ X
     │         │
     │         │ f
     ↓         ↓
 Spec κ(y) ──→ Y
```
-/
instance isProper_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsProper (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The structure morphism `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a universally
closed morphism `f : X ⟶ Y` over `y : Y` is universally closed, being the base change of `f`
along `Spec κ(y) ⟶ Y`. -/
instance universallyClosed_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] (y : Y) : UniversallyClosed (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- **The global sections of a proper integral scheme over an algebraically closed field.**

For `X` proper and integral over an algebraically closed field `K`, the structure morphism
induces an isomorphism `K ≅ Γ(X, 𝒪_X)`. This is `lem:cube-global-sections` of the blueprint.

Mathlib's `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` makes `Γ(X, 𝒪_X)` an
integral extension of `K`, and it is a domain because `X` is integral; over an algebraically
closed `K` an integral domain extension is trivial. -/
theorem isIso_ΓSpecIso_inv_comp_appTop {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π] :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
  apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed π

/-- **A proper affine morphism is finite.** A morphism of schemes is integral exactly when it is
universally closed and affine, and finite exactly when it is integral and locally of finite
type; a proper morphism is universally closed and locally of finite type by definition. -/
theorem isFinite_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsProper f] :
    IsFinite f :=
  have : IsIntegralHom f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨this, inferInstance⟩

section ProperAffine

variable (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- **A proper affine scheme over a field is finite over that field**, being the composite of
`isFinite_of_isAffineHom` with the fact that a morphism between affine schemes is affine. This
is the second assertion of the blueprint's `lem:deg-proper-affine-finite`; the identification
`X ≅ Spec Γ(X, 𝒪_X)` it is phrased with is `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem isFinite_of_isAffine [IsAffine X] [IsProper f] : IsFinite f :=
  isFinite_of_isAffineHom f

/-- **The global sections of a proper affine scheme over a field form a finite-dimensional
algebra over that field.** This is the first assertion of the blueprint's
`lem:deg-proper-affine-finite`. -/
theorem finite_ΓSpecIso_inv_comp_appTop [IsAffine X] [IsProper f] :
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.Finite := by
  have : IsFinite f := isFinite_of_isAffine K f
  apply RingHom.finite_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact IsFinite.finite_app f ⊤ (isAffineOpen_top _)

/-- **A proper affine scheme over a field has dimension at most zero.**

This is the last assertion of the blueprint's `lem:deg-proper-affine-finite`, and the one the
hyperplane section argument consumes: a component of the support of a coherent sheaf on which a
very ample section does not vanish is a closed subscheme of an affine open, hence proper and
affine, hence a point.

Its global sections are a finite-dimensional algebra over a field, hence an Artinian ring, so
every prime of `Γ(X, 𝒪_X)` is maximal and `Spec Γ(X, 𝒪_X) ≅ X` has Krull dimension at most
zero. -/
theorem topologicalKrullDim_le_zero_of_isAffine [IsAffine X] [IsProper f] :
    topologicalKrullDim X ≤ 0 := by
  have hF := finite_ΓSpecIso_inv_comp_appTop K f
  algebraize [((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom]
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K _
  rw [IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum Γ(X, ⊤)) ≤ 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  simpa using Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 Γ(X, ⊤))

end ProperAffine

end AlgebraicGeometry
